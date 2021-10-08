set -e
#set -x
for elem in *.exe; do
    echo $elem

    data="$elem.db"
   # if [ -f $data ]; then
   #     if [ $(chop list samples --data $data | wc -l) -gt 20000 ]; then
   #         exit
   #         continue
   #     fi
   # fi

    echo chop sample -data $data -events CYCLES -period 100000 ./$elem
    if [ ! -f $data ]; then
        for rep in $(seq 1 10); do
            echo $rep $rep $rep
            chop sample -data $data -events CYCLES -period 100000 ./$elem
        done;

        chop list samples --data $data | wc -l > $elem.samples
        if [ $(cat $elem.samples) -lt 10000 ]; then
            echo check sampling method. Too few samples to proceed.
            continue
        fi
    elif [ ! -f $elem.samples ]; then
        chop list samples --data $data | wc -l > $elem.samples
    fi

    if [ $(cat $elem.samples) -lt 10000 ]; then
        echo check sampling method. Too few samples to proceed.
        continue
    fi

    if [ ! -f $elem.functions ]; then
        chop disasm -data $data ./$elem $(ldd ./$elem | cut -d " " -f 3 | grep -v libc.so)
        chop count -data $data
        chop annotate -data $data
        chop list functions -data $data > $elem.functions
    fi

    if [ ! -f $elem.functions_selected ]; then
        set +e
        chop-score-table $data 80 10 1 -functions > $elem.functions_selected
        error=$?
        set -e
        if [ $error -ne 0 ]; then
            rm -f $elem.functions_selected
            continue
        fi
    fi

    for mfunc in $(cat $elem.functions_selected); do
        echo chop-marks-sysz ./$elem $mfunc
        tracepoints=$(chop-marks-sysz ./$elem $mfunc)
        score=$(cat $elem.functions | tr "\t" " " | grep " $mfunc " | cut -d ' ' -f 5 | cut -d "." -f 1 | xargs printf "%03d\n")
        tracedir="$elem#$score#$mfunc.trace"
        mptdir="$elem#$score#$mfunc.mpt"

        if [ ! -f $tracedir/OK ]; then
            rm -fr $tracedir
            set +e
            echo timeout 60 chop trace -log-level verbose $tracepoints -max-traces 10 -access-trace -gzip -trace-dir $tracedir ./$elem
            timeout 60 chop trace -log-level verbose $tracepoints -max-traces 10 -access-trace -gzip -trace-dir $tracedir ./$elem
            error=$?
            set -e
            if [ $error -eq 0 ]; then
                touch $tracedir/OK
            fi
        fi

        if [ ! -f $mptdir/OK ] && [ -f $tracedir/OK ]; then
            rm -fr $mptdir
            mkdir $mptdir
            set +e
            chop-trace2mpt --trace-dir $tracedir -o "$mptdir/$elem#$score#$mfunc#all" --gzip
            error=$?
            chop-trace2mpt --trace-dir $tracedir -o "$mptdir/$elem#$score#$mfunc#user" --gzip --max-address 0x30000000000
            error=$((error+$?))
            set -e
            if [ $error -eq 0 ]; then
                touch $mptdir/OK
            fi
        fi
    done;
    echo $elem done
done;
