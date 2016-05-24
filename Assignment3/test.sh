#!/bin/bash
DIR="res/"
LOWER=3
BIGGER=10

mkdir -p res
rm -f ${DIR}*.tmp
rm -f ${DIR}*.log

echo "Starting tests..."
sed -i "s/concurrentTransactions(3, 3, 20, 10)/concurrentTransactions(2, 2, 2, 2)/g" bank/TestHarness.java
timeout 600 bash bank.sh >> ${DIR}0.tmp
sed -i "s/concurrentTransactions(2, 2, 2, 2)/concurrentTransactions(3, 3, 20, 10)/g" bank/TestHarness.java
grep time ${DIR}0.tmp -A 7 > ${DIR}0.log

for j in `seq 1 4`; do
	echo "Changing argument $j"
	for i in `seq $LOWER $BIGGER`; do
		((a= $j == 1 ? $i : 2))
		((b= $j == 2 ? $i : 2))
		((c= $j == 3 ? $i : 2))
		((d= $j == 4 ? $i : 2))
		sed -i "s/concurrentTransactions(3, 3, 20, 10)/concurrentTransactions($a, $b, $c, $d)/g" bank/TestHarness.java
		timeout 600 bash bank.sh >> "${DIR}$j.tmp"
		echo -e "\n----- TEST a=$a b=$b c=$c d=$d END----------\n" >> "${DIR}$j.tmp"
		echo "Test with a=$a b=$b c=$c d=$d finished. Writing in temporary result to ${DIR}$j.tmp"
		sed -i "s/concurrentTransactions($a, $b, $c, $d)/concurrentTransactions(3, 3, 20, 10)/g" bank/TestHarness.java
	done
	grep "elapsed time" "${DIR}$j.tmp" -A 7 > "${DIR}$j.log"
done

echo "Tests are done. Look in ${DIR} for results."
rm -f ${DIR}*.tmp
