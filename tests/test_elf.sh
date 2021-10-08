set -e
if [ -f $1.OK ]; then
    cat $1.OK
    exit
fi
if [ -f $1.FAIL ]; then
    cat $1.FAIL
    exit
fi
file=$(mktemp)
set +e
timeout 10 gdb -batch -x gdb.command $1 2> /dev/null > $file
set -e
loops=$(cat $file | grep -c START_TEST)
if [ $loops -gt 1 ]; then
    echo OK $loops | tee $1.OK
    stat=OK
else 
    echo FAIL | tee $1.FAIL
    stat=FAIL
    cat $file >> $1.FAIL
fi

set +e
perf stat -r 10 timeout 10 $1 2>> $1.$stat >> $1.$stat 

instructions=$(cat $1.$stat | grep instructions:u | tr -s ' ' | cut -d " " -f 2 | tr -d ",")
cycles=$(cat $1.$stat | grep cycles:u | tr -s ' ' | cut -d " " -f 2 | tr -d ",")

echo INSTRUCTIONS $instructions | tee -a $1.$stat 
echo CYCLES $cycles | tee -a $1.$stat 

echo "INSTRxCALL" $(echo "$instructions / $loops" | bc -l) | tee -a  $1.$stat 
echo "CYCxCALL" $(echo "$cycles / $loops" | bc -l) | tee -a  $1.$stat 

set -e

rm -f $file
