#!/bin/bash

function make_execs() {
  mkdir -p $outpath/cmp_errors_tmp
  for i in $threads_ids; do
    r_bits=$((rbitsA + i*rbitsB))
    echo "Compiling code for level = $level using r_bits = $r_bits"
    make clean; make CC=gcc LEVEL=$level $avx_str TEST_PICKYFIX=1 R_BITS=$r_bits compare_n_errors 1> /dev/null
    cp ./bin/compare_n_errors $outpath/cmp_errors_tmp/compare_n_errors$i
  done
}

function run_cmp_errors() {
  thread=$1
  path=$2

  $outpath/cmp_errors_tmp/compare_n_errors$i $n_tests $(( seed + thread )) $thread > $path/output_level$level.part$thread
  pids[${i}]=$!
}


if [ "$#" -ne 4 ]; then
  echo "Usage: $0 <output path> <level> <n_tests> <'AVX512=1' | 'AVX2=1' | ''> " >&2
  exit 1
fi

outpath=$1
level=$2
n_tests=$3
avx_str=$4

mkdir -p $outpath
threads_ids=`seq 0 23`


if [ $level -eq 1 ]; then
  rbitsA=9201
  rbitsB=100
  seed=1
elif [ $level -eq 3 ]; then
  rbitsA=19201
  rbitsB=100
  seed=0
elif [ $level -eq 5 ]; then
  rbitsA=33201
  rbitsB=100
  seed=0
else
  echo "INVALID LEVEL."
  exit 1
fi



rm -f $outpath/cmp_errors_tmp/*
rm -f $outpath/*.part*
make_execs
for i in $threads_ids; do
  run_cmp_errors $i $outpath &
  pids[${i}]=$!
done

echo "Running!"

for pid in ${pids[*]}; do
    wait $pid
done

echo "All threads finished."
cat $outpath/*.part* > $outpath/output$level.csv
echo "Results in $outpath/output$level.csv : )".
