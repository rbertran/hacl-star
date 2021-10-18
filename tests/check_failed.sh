tmp=$(mktemp)
for elem in */*all*reset*FAIL ; do
    #echo $elem
    bname=${elem/%_reset.elf.FAIL/}
    address=$(zgrep PSW_ADDR $bname.mps.gz | cut -d ' ' -f 3 )
    if [ $(echo $address | grep -c 0x0000000001) -gt 0 ]; then
        name=$(dirname $elem)
        log=${name/%.mpt/.log}
        if [ $(grep -c call $log) -eq  0 ]; then
            # no system call
            segfault=$(timeout 10 gdb -batch -x gdb.command ${elem/%.FAIL/} 2> /dev/null | grep " in " | tail -n 1 | cut -d " " -f 1 | sed "s/0x//g" | sed "s/^0*//")
            #timeout 10 gdb -batch -x gdb.command ${elem/%.FAIL/} 2> /dev/null 

            timeout 10 gdb -batch -x gdb.command2 ${elem/%.FAIL/} > $tmp
            for num in $(seq 0 15); do
                # if [ $num -eq 10 ]; then continue; fi
                if [ $num -eq 14 ]; then continue; fi

                val=$(cat $tmp | grep "^r$num " | tr -s " " | cut -d ' ' -f 2)
                val="R GR$num $(printf "0x%016X" $val)"
                #echo $val
                if [ $(zgrep -c "$val" ${elem/%_reset.elf.FAIL/.mps.gz}) -eq  0 ]; then
                    echo $elem
                    echo $num
                    echo "Found " $val
                    zgrep "R GR$num " ${elem/%_reset.elf.FAIL/.mps.gz}
                    exit
                fi
            done;

            for num in $(seq 0 15); do
                val=$(cat $tmp | grep "^f$num " | tr -s " " | cut -d ' ' -f 4 | sed "s/)//") 
                val="R FPR$num $(printf "0x%016X" $val)"
                if [ $(zgrep -c "$val" ${elem/%_reset.elf.FAIL/.mps.gz}) -eq  0 ]; then
                    echo $elem
                    echo $num
                    echo "Found" $val
                    zgrep "R FPR$num " ${elem/%_reset.elf.FAIL/.mps.gz}
                    exit
                fi
            done;

            for num in $(seq 0 31); do
                val1=$(cat $tmp | grep "^v$num " | cut -d "=" -f 7 | cut -d ',' -f 2 | sed "s/}//") 
                val2=$(cat $tmp | grep "^v$num " | cut -d "=" -f 7 | cut -d ',' -f 1 | sed "s/{//") 
                #echo $val1 $val2
                val="R VR$num $(printf "0x%016X%016X" $val2 $val1)"
                #echo $val
                if [ $(zgrep -c "$val" ${elem/%_reset.elf.FAIL/.mps.gz}) -eq  0 ]; then
                    echo $elem
                    echo $num
                    echo "Found" $val
                    zgrep "R VR$num " ${elem/%_reset.elf.FAIL/.mps.gz}
                fi
            done;

            if [ $(objdump -d  ${elem/%.FAIL/} | cut -d ":" -f 1 | grep -c $segfault) -ne 0 ]; then
                # Fail in a instruction 
                echo $address $elem $segfault $(objdump -d ${elem/%.FAIL/} | grep $segfault)
            else
                # Fail because code not found
                # 
                # Possible source targets:
                echo $address $elem $segfault JUMP
            fi
        fi
    else
        echo $elem bad address, system call probably
    fi
done;
