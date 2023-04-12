#!/bin/bash

function make_execs() {
  mkdir -p $outpath/execs
  for i in $threads_ids; do
    r_bits=$((rbitsA + i*rbitsB))
    echo "Compiling code for level = $level using r_bits = $r_bits"
    make clean; make CC=gcc LEVEL=$level $avx_str TEST_BGF=1 TEST_PICKYFIX=1 R_BITS=$r_bits threshold 1> /dev/null
    cp ./bin/threshold $outpath/execs/threshold$i
  done
}

function run_threshold_exec() {
  thread=$1
  path=$2

  $outpath/execs/threshold$i $n_tests $thread $thread > $path/output_level$level.part$thread
  pids[${i}]=$!
}



if [ "$#" -ne 4 ] || ! [ -d "$1" ]; then
  echo 'Usage: $0 <output path> <level> <n_tests> <"AVX512=1" | "AVX2=1" | ""> ' >&2
  exit 1
fi

outpath=$1
level=$2
n_tests=$3
avx_str=$4

threads_ids=`seq 0 47`


if [ $level -eq 1 ]; then
  rbitsA=9001
  rbitsB=100
elif [ $level -eq 3 ]; then
  rbitsA=19001
  rbitsB=200
elif [ $level -eq 5 ]; then
  rbitsA=33201
  rbitsB=200
else
  echo "INVALID LEVEL."
  exit 1
fi

rm -f $outpath/execs/*
make_execs
rm -f $outpath/*.part*
for i in $threads_ids; do
  run_threshold_exec $i $outpath &
  pids[${i}]=$!
done

echo "Running!"

for pid in ${pids[*]}; do
    wait $pid
done

echo "All threads finished."
cat $outpath/*.part* > $outpath/output$level.csv
echo "Results in $outpath/output$level.csv : )".
