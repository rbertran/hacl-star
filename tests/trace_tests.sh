set -e
#set -x

# Your path to the toolchain
export PATH=/opt/rh/gcc-toolset-10/root/bin/:$PATH

# Path to chopstix
CHOPSTIX=/home/ramon/chopstix-install

# Path to microprobe
MICROPROBE=/home/ramon/microprobe


###########################################


if [ ! -e $MICROPROBE/venv ]; then
    cd $MICROPROBE
    ./bootstrap_environment.sh 3
    cd - > /dev/null 2>/dev/null
fi

cd $MICROPROBE
source activate_microprobe
cd - > /dev/null 2>/dev/null

source $CHOPSTIX/share/chopstix/setup.sh

# compile tests
make -f Makefile.static

for elem in *.exe; do
    echo $elem

    data="$elem.db"

   # if [ -f $data ]; then
   #     if [ $(chop list samples --data $data | wc -l) -gt 20000 ]; then
   #         exit
   #         continue
   #     fi
   # fi


    # Sample ten times each binary to reliably detect the functions
    # where most cycles are spent (hot functions)

    echo chop sample -data $data -events CYCLES -period 100000 ./$elem
    if [ ! -f $data ]; then
        for rep in $(seq 1 10); do
            echo $rep $rep $rep
            chop sample -data $data -events CYCLES -period 100000 ./$elem
        done;

        chop list samples --data $data | wc -l > $elem.samples
        if [ $(cat $elem.samples) -lt 10000 ]; then
            echo check sampling method. Too few samples to proceed. | tee $elem.error
            continue
        fi
    elif [ ! -f $elem.samples ]; then
        chop list samples --data $data | wc -l > $elem.samples
    fi

    if [ $(cat $elem.samples) -lt 10000 ]; then
        echo check sampling method. Too few samples to proceed. | tee $elem.error
        continue
    fi

    #
    # Post process the sampling database to link the sample point to the 
    # assembly functions, and list all the functions information
    #
    if [ ! -f $elem.functions ]; then
        chop disasm -data $data ./$elem $(ldd ./$elem | cut -d " " -f 3 | grep -v libc.so)
        chop count -data $data
        chop annotate -data $data
        chop list functions -data $data > $elem.functions
    fi

    #
    # Select hot functions: 80% of coverage, up to 10 total functions, and
    # we don't care abount the minimum size (1).
    #
    if [ ! -f $elem.functions_selected ]; then
        set +e
        chop-score-table $data 80 10 1 -functions > $elem.functions_selected
        error=$?
        set -e
        if [ $error -ne 0 ]; then
            rm -f $elem.functions_selected
            echo Unable to compute the functions selected | tee $elem.error
            continue
        fi
    fi

    #
    # For each function selected, generate the trace and then, the corresponding
    # MPT and then the corresponding AVP for simulation
    #
    for mfunc in $(cat $elem.functions_selected); do
        echo chop-marks-sysz ./$elem $mfunc
        tracepoints=$(chop-marks-sysz ./$elem $mfunc)
        score=$(cat $elem.functions | tr "\t" " " | grep " $mfunc " | cut -d ' ' -f 5 | cut -d "." -f 1 | xargs printf "%03d\n")
        tracedir="$elem#$score#$mfunc.trace"
        mptdir="$elem#$score#$mfunc.mpt"

        #
        # Trace
        #
        if [ ! -f $tracedir/OK ]; then
            rm -fr $tracedir
            set +e
            echo timeout 60 chop trace -log-level verbose $tracepoints -max-traces 10 -access-trace -gzip -trace-dir $tracedir ./$elem
            timeout 60 chop trace -log-level verbose $tracepoints -max-traces 10 -access-trace -gzip -trace-dir $tracedir ./$elem
            error=$?
            set -e
            if [ $error -eq 0 ]; then
                touch $tracedir/OK
            else
                echo Unable to trace | tee $tracedir.error
                continue
            fi
        fi

        #
        # Convert to MPT
        #
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
            else
                echo Unable to convert to mpt | tee $tracedir.error
                continue
            fi
        fi

        #
        # Convert to standalone ELF ?
        #
        for mptfile in $mptdir/*mpt.gz ; do
            if [ ! -f ${mptfile/%.mpt.gz/.s} ]; then
                set +e
                echo mp_mpt2elf.py -t $mptfile -T z16-z16-z64_linux_gcc -O ${mptfile/%.mpt.gz/.s} --raw-bin --compiler /opt/rh/gcc-toolset-10/root/bin/gcc --wrap-endless
                mp_mpt2elf.py -t $mptfile -T z16-z16-z64_linux_gcc -O ${mptfile/%.mpt.gz/.s} --raw-bin --compiler /opt/rh/gcc-toolset-10/root/bin/gcc --wrap-endless & 
                set -e
            fi

            if [ ! -f ${mptfile/%.mpt.gz/_reset.s} ]; then
                set +e
                echo mp_mpt2elf.py -t $mptfile -T z16-z16-z64_linux_gcc -O ${mptfile/%.mpt.gz/_reset.s} --raw-bin --compiler /opt/rh/gcc-toolset-10/root/bin/gcc --wrap-endless --reset 
                mp_mpt2elf.py -t $mptfile -T z16-z16-z64_linux_gcc -O ${mptfile/%.mpt.gz/_reset.s} --raw-bin --compiler /opt/rh/gcc-toolset-10/root/bin/gcc --wrap-endless --reset & 
                set -e
            fi
        done;
        wait

        #
        # Need to compile manually
        #
        for asmfile in $mptdir/*.s ; do
            if [ ! -f ${asmfile/%.s/.elf} ]; then
                set +e
                echo /opt/rh/gcc-toolset-10/root/bin/gcc ${asmfile} -o ${asmfile/%.s/.elf} -T ${asmfile/%.s/.ldscript} -T /home/ramon/microprobe/targets/z/templates/z16-z16-z64_linux_gcc.ldscript -march=z15
                /opt/rh/gcc-toolset-10/root/bin/gcc ${asmfile} -o ${asmfile/%.s/.elf} -T ${asmfile/%.s/.ldscript} -T /home/ramon/microprobe/targets/z/templates/z16-z16-z64_linux_gcc.ldscript -march=z15 
                if [ ! -f ${asmfile/%.s/.elf} ]; then
                    echo /opt/rh/gcc-toolset-10/root/bin/gcc ${asmfile} -o ${asmfile/%.s/.elf} -T ${asmfile/%.s/.ldscript} -T /home/ramon/microprobe/targets/z/templates/z16-z16-z64_linux_gcc.ldscript -march=z15 -static
                    /opt/rh/gcc-toolset-10/root/bin/gcc ${asmfile} -o ${asmfile/%.s/.elf} -T ${asmfile/%.s/.ldscript} -T /home/ramon/microprobe/targets/z/templates/z16-z16-z64_linux_gcc.ldscript -march=z15 -static
                fi
                set -e
            fi
        done

        #
        # Try if the run 
        #
        for elffile in $mptdir/*elf ; do
            set +e
            test_elf.sh ${elffile} & 
            set -e
        done;
        wait

        #
        # Convert to AVP
        #
        for mptfile in $mptdir/*mpt.gz ; do
            if [ ! -f ${mptfile/%.mpt.gz/.avp.gz} ]; then
                set +e
                echo mp_mpt2avp.py -t $mptfile -T z16-z16-z64_mesa_st -O ${mptfile/%.mpt.gz/.avp.gz} --raw-bin --wrap-endless  
                mp_mpt2avp.py -t $mptfile -T z16-z16-z64_mesa_st -O ${mptfile/%.mpt.gz/.avp.gz} --raw-bin --wrap-endless & 
                set -e
            fi

            if [ ! -f ${mptfile/%.mpt.gz/_reset.avp.gz} ]; then
                set +e
                echo mp_mpt2avp.py -t $mptfile -T z16-z16-z64_mesa_st -O ${mptfile/%.mpt.gz/_reset.avp.gz} --raw-bin --wrap-endless --reset  
                mp_mpt2avp.py -t $mptfile -T z16-z16-z64_mesa_st -O ${mptfile/%.mpt.gz/_reset.avp.gz} --raw-bin --wrap-endless --reset & 
                set -e
            fi
        done;
        wait

    done;
    echo $elem done
done;

echo TRACED $(ls */*mpt.gz | wc -l)
echo GENERATED $(ls */*.s | wc -l)
echo GENERATED RESET $(ls */*reset.s | wc -l)
echo COMPILED $(ls */*.elf | wc -l)
echo COMPILED RESET $(ls */*reset.elf | wc -l)
echo RUNOK $(ls */*.elf.OK | wc -l)
echo RUNFAIL $(ls */*.elf.FAIL | wc -l)
echo RUNOK RESET $(ls */*reset.elf.OK | wc -l)
echo RUNFAIL RESET $(ls */*reset.elf.FAIL | wc -l)
