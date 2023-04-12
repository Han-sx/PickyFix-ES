# Faster constant-time decoder for MDPC codes and applications to BIKE KEM

__Authors__: Thales Paiva and Routo Terada


**Table of Contents**
<!-- MarkdownTOC -->

- Abstract
- System setup
- What is included in this repository
- BIKE code - Compiling and Running
    - Compilation Flags
    - The need for `make clean` when parameters change
    - Example
- Reproducibility
    - Counters
        - Data to be reproduced
        - Steps to reproduce
        - Data format
    - Comparison of errors left
        - Small example
        - Data to be reproduced
        - Steps to reproduce
    - Thresholds
        - Data to be reproduced
        - Steps to reproduce
    - DFR
        - Data to be reproduced
        - Steps to reproduce
    - Concavity
        - Data to be reproduced
        - Steps to reproduce
    - Performance
        - Data to be reproduced
        - Steps to reproduce
- Figures
- Exploring the PickyFix code
- Conclusion

<!-- /MarkdownTOC -->

# Abstract

This README serves as a guide to the supplementary material of our submission
to CHES 2022. Our 3 main objectives are:

1. Explain how to reproduce our results
1. Identify our main original contribution - the implementation of PickyFix
1. Explain our data and the corresponding visualization tools

**Important notice**: Our implementation is based on [BIKE Additional Implementation](https://bikesuite.org/files/round2/add-impl/BIKE_Additional.2020.02.09.zip) by Drucker, Kostic and Gueron.
Therefore, most of the code in the `bike` directory comes from their implementation.
Our implementation of PickyFix is meant to be plugged in to their implementation, we tried to
isolate the majority of our code into the `bike/pickyfix` directory.

# System setup:

We tested the code under the following systems:

## Server 1

```
$ gcc --version
gcc (GCC) 11.1.0
$ cat /proc/cpuinfo | grep "model name" | head -n 1
model name  : Intel(R) Xeon(R) Gold 5118 CPU @ 2.30GHz
$ pipenv --version
pipenv, version 2021.5.29
$ python --version
Python 3.9.5
```

## Server 2

```
$ gcc --version
gcc (Debian 10.2.1-6) 10.2.1 20210110
$ cat /proc/cpuinfo | grep "model name" | head -n 1
model name  : Intel(R) Xeon(R) Gold 6148 CPU @ 2.40GHz
$ pipenv --version
pipenv, version 2022.4.8
$ python --version
Python 3.9.2
```

# What is included in this repository

* `bike`: The source code of BIKE and our decoder.
            **Most of this directory consists of BIKE Additional Implementation,
            which is not our work.**
            Therefore, we only enumerate below the directories with our contributions:

    * `bike/experiments`: Each source in `bike/experiments` will
        generate an executable that outputs a CSV corresponding to one experiment. This
        is how we generated the data for most of the figures and tables in the paper.

        * `bike/experiments/compare_n_errors.c`: The experiment to compare the number of errors
            left after one iteration of BGF and PickyFix with different values of `n_flips`.
        * `bike/experiments/counters.c`: The experiment to compute the UPC counters.
        * `bike/experiments/experiments.h`: Some common functions and definitions for the
            majority of experiments.
        * `bike/experiments/kem_internals.h`: Some static functions that are defined in
            BIKE Additional Implementation `kem.c`, that are also used in our experiments.
            Since we wanted to make the minimum amount of changes to BIKE Additional Implementation,
            we preferred this approach instead of altering the functions to be non-static.
        * `bike/experiments/main.c`: The main experiment used in this paper: the Decryption Failure
        Rate (DFR) estimation for applying Vasseur's extrapolation framework.
        * `bike/experiments/threshold.c`: The experiment to compute the thresholds used by BGF.

    * `bike/pickyfix`: This is where our implementation of PickyFix lives.
        * `bike/pickyfix/decode_internals.h`: Some static functions from the BGF decoder (
            that lives in `decode/decode.c`). These functions are important for syndrome
            recomputation and other common steps to bit-flipping decoding.
        * `bike/pickyfix/pickyfix.c`: The entry point for the PickyFix decoder.
        * `bike/pickyfix/pickyfix.h`: Definitions such as `n_flips` for each level and additional
            `structs` and `typedefs`.
        * `bike/pickyfix/Makefile`: The partial Makefile for this directory.
        * `bike/pickyfix/secure_pickyfix_avx2.c`: The AVX2 implementation of PickyFix.
            **NOTICE: AT THIS MOMENT, THIS IS JUST A COPY OF THE PORTABLE IMPLEMENTATION.**
            We named it this way because of how the building process works.
        * `bike/pickyfix/secure_pickyfix_avx512.c`: The AVX512 implementation of PickyFix.
        * `bike/pickyfix/secure_pickyfix_portable.c`: The portable implementation of PickyFix.

    * `bike/run_compare_n_errors.sh`: Script to run instances of `bike/experiments/compare_n_errors.c`.
    * `bike/run_performance_test.sh`: Script to run instances of `bike/experiments/perf.c`.
    * `bike/run_threshold.sh`: Script to run instances of `bike/experiments/threshold.c`.

* `data`: CSV files for results and setup of our experiments.
            Each of its sub-directories correspond to a different experiment and contains
            a set of CSV files.
            The contents of this directory will be seen in more detail when discussing
            the reproducibility.

* `analysis/dfr_experiment.py`: The `python` program to execute the DFR extrapolation experiment.
* `analysis/plotters/plots.py`: The `python` program to plot the data.

# BIKE code - Compiling and Running

Since we based our implementation in BIKE Additional Implementation by Drucker et al., we
kept the same building mechanism as they used.

## Compilation Flags


**Most important compilation flags inherited from BIKE Additional Implementation**:

 - `USE_NIST_RAND` : Use the RNG from NIST.
 - `USE_OPENSSL`   : Use OpenSSL for AES/SHA and GF2X multiplication.
                   OpenSSL must be installed on the platform.
 - `OPENSSL_DIR`   : Set the path of the OpenSSL include/lib directories.
 - `RDTSC`         : Measure time in cycles rather than in milliseconds.
 - `VERBOSE`       : Add verbose (level:1-4 default:1).
 - `AVX2`          : Compile with AVX2 support (to compile use GCC).
 - `AVX512`        : Compile with AVX512 support (to compile use GCC).
 - `LEVEL`         : Security level (1/3/5).

**Additional compilation flags we used**:

 - `R_BITS`: Defines the value of parameter `R_BITS` to be used for testing. This is specially important
    for the DFR extrapolation framework.
 - `ERROR_WEIGHT`: Defines the value of the error weight `T1` used for encryption. This is used for the concavity
    tests with the exaggerated error weight.
 - `TEST_PICKYFIX`: Use the PickyFix decoder.
 - `TEST_BGF`: Use the BGF decoder.
 - `MAX_IT`: Set the number of iterations for the decoders to use.

## The need for `make clean` when parameters change

We highly recommend that you run `make clean` when you change the compilation flags, otherwise the compiler
may have problems.

## Example

First `cd` to the `bike` directory. Then call `make` with the appropriate parameters.


Let us compile and test the PickyFix and BGF decoder in a system supporting AVX2 instructions for
`LEVEL = 1`. Since we want to see failures occurring, let us select the reduced value of `R_BITS = 9901`.
```
$ make clean; make LEVEL=1 TEST_PICKYFIX=1 TEST_BGF=1 AVX2=1 R_BITS=9901
```
Let us see the arguments we can pass to the `./bin/main`, which consists of the simple DFR experiment.
```
$ ./bin/main
Usage: ./bin/main <number of tests> <seed> <number of threads> [measure time (true|False)]
```
Now let us run it with 1 thread and see the result. See how it prints partial results to `stderr` with intervals
of 1000 tests. Furthermore, the last two rows show the final result: PickyFix failed in 35 while BGF
failed in 50 out of 10,000 tests.
```
$ time ./bin/main 10000 1 1
decoder,n_iterations,level,r_bits,error_weight,n_failures,n_tests
BGF,5,1,9901,134,7,1000,thread0
PickyFix,5,1,9901,134,4,1000,thread0
BGF,5,1,9901,134,10,2000,thread0
PickyFix,5,1,9901,134,9,2000,thread0
BGF,5,1,9901,134,14,3000,thread0
PickyFix,5,1,9901,134,13,3000,thread0
BGF,5,1,9901,134,18,4000,thread0
PickyFix,5,1,9901,134,14,4000,thread0
BGF,5,1,9901,134,26,5000,thread0
PickyFix,5,1,9901,134,16,5000,thread0
BGF,5,1,9901,134,28,6000,thread0
PickyFix,5,1,9901,134,19,6000,thread0
BGF,5,1,9901,134,31,7000,thread0
PickyFix,5,1,9901,134,25,7000,thread0
BGF,5,1,9901,134,38,8000,thread0
PickyFix,5,1,9901,134,30,8000,thread0
BGF,5,1,9901,134,42,9000,thread0
PickyFix,5,1,9901,134,31,9000,thread0
BGF,5,1,9901,134,50,10000,thread0
PickyFix,5,1,9901,134,35,10000,thread0
BGF,5,1,9901,134,50,10000
PickyFix,5,1,9901,134,35,10000
./bin/main 10000 1 1  28.46s user 0.00s system 99% cpu 28.481 total
```

While this is a nice result for PickyFix vs. BGF, both using the default number of iterations `MAX_IT=5`, this
does not really say very much: a good decoder must perform well under the DFR extrapolation framework.
Next, we will see how to reproduce our results for the DFR extrapolation used in the paper.


# Reproducibility

We will now discuss how to reproduce the results presented in our paper.
Since all results are contained in the `data/` directory, we will describe how each of the data
was generated.

**Important:** The results are meant to be fully reproducible when using the same seeds and number of threads.
If you found different results, please contact us so we can better understand what happened.

**Important:** We recommend you use [Pipenv](https://pypi.org/project/pipenv/) to install
the dependencies for the auxiliary python scripts.

## Counters

Let us start with the simple experiment: determine the UPC values for each counter

### Data to be reproduced

* `data/counters/counters_level5.csv`

This data file is used in Figure 2.

### Steps to reproduce

Let us compile and run the experiment and check that the reproduced data is indeed equal to our data file.
```
$ mkdir -p reproduced/counters
$ make clean; make LEVEL=5 TEST_PICKYFIX=1 AVX2=1
$ ./bin/counters 10 > reproduced/counters/counters_level5.csv
$ diff reproduced/counters/counters_level5.csv ../data/counters/counters_level5.csv
```

Now let us see the file generated.
```
$ head reproduced/counters/counters_level5.csv
level,r_bits,error_weight,test,counter,n_right,n_wrong
# 0,threshold=86
5,40973,264,0,0,0,0
5,40973,264,0,1,0,0
5,40973,264,0,2,0,0
5,40973,264,0,3,0,0
5,40973,264,0,4,0,0
5,40973,264,0,5,0,0
5,40973,264,0,6,0,0
5,40973,264,0,7,0,0
```

### Data format

* `#`: Lines starting with `#` are comments
* `level`: The security level (1/3/5)
* `r_bits`: The value of `R_BITS`
* `error_weight`: The weight of the encryption error
* `test`: The ID of the test (remember we ran 1 test)
* `counter`: The UPC value between `0` and `DV`
* `n_right`: Number of occurrences of the UPC `counter` within the `R_BITS - error_weight` right entries
* `n_wrong`: Number of occurrences of the UPC `counter` within the `error_weight` wrong entries

## Comparison of errors left

The code for this test is in `bike/experiments/compare_n_errors.c`. It consists of computing
the average number of errors left after one iteration of BGF and one iteration of FixFlip with
different values of `nflips`.

Since this test is rather expensive, we let `nflips` be a multiple of five, and it is updated
according to the main for loop:
```c
for (int nflips = 5; nflips <= MIN(T1, 200); nflips += 5)
```

To run this experiment, we use the shell script `bike/run_compare_n_errors.sh`.
Given a security level (1/3/5), this will first build 24 executables for different numbers of `R_BITS`
and then run 24 threads of the `bike/experiments/compare_n_errors.c` program. If you may need to adjust the
code to your needs, according to the number of cores you are using.

### Small example

If you just want to examine the data with a quick test, just set a small value of `n_tests`. It
will take about 1 minute to compile all the different executable files, but it will not take too long to finish.
```
$ time ./run_compare_n_errors.sh output_compare_n_errors 1 10 AVX2=1
Compiling code for level = 1 using r_bits = 9201
Compiling code for level = 1 using r_bits = 9301
Compiling code for level = 1 using r_bits = 9401
Compiling code for level = 1 using r_bits = 9501
Compiling code for level = 1 using r_bits = 9601
Compiling code for level = 1 using r_bits = 9701
Compiling code for level = 1 using r_bits = 9801
Compiling code for level = 1 using r_bits = 9901
Compiling code for level = 1 using r_bits = 10001
Compiling code for level = 1 using r_bits = 10101
Compiling code for level = 1 using r_bits = 10201
Compiling code for level = 1 using r_bits = 10301
Compiling code for level = 1 using r_bits = 10401
Compiling code for level = 1 using r_bits = 10501
Compiling code for level = 1 using r_bits = 10601
Compiling code for level = 1 using r_bits = 10701
Compiling code for level = 1 using r_bits = 10801
Compiling code for level = 1 using r_bits = 10901
Compiling code for level = 1 using r_bits = 11001
Compiling code for level = 1 using r_bits = 11101
Compiling code for level = 1 using r_bits = 11201
Compiling code for level = 1 using r_bits = 11301
Compiling code for level = 1 using r_bits = 11401
Compiling code for level = 1 using r_bits = 11501
Running!
All threads finished.
Results in output_compare_n_errors/output1.csv : ).
./run_compare_n_errors.sh output_compare_n_errors 1 10 AVX2=1  64.92s user 4.63s system 116% cpu 59.639 total
```

### Data to be reproduced

* `data/compare_n_errors/n_errors.csv`

This data file is used in Figure 6 and Table 3.

### Steps to reproduce

Let us compile and run the experiment and check that the reproduced data is indeed equal to our data file.
```shell
$
for level in 1 3 5; do
    mkdir -p reproduced/compare_n_errors/tmp$level
    # YOU MAY NEED TO ADJUST TO YOUR AVX SUPPORT BELOW
    time ./run_compare_n_errors.sh reproduced/compare_n_errors/tmp$level $level 10000 AVX512=1
done
$ head -n 1 reproduced/compare_n_errors/tmp1/output1.csv > reproduced/compare_n_errors/header.csv
$ tail -q -n +2 reproduced/compare_n_errors/tmp1/output1.csv \
    reproduced/compare_n_errors/tmp3/output3.csv \
    reproduced/compare_n_errors/tmp5/output5.csv > reproduced/compare_n_errors/body.csv
$ cat reproduced/compare_n_errors/header.csv \
      reproduced/compare_n_errors/body.csv > reproduced/compare_n_errors/n_errors.csv
```

## Thresholds

The way this experiment works is very similar to the experiment above, but it is much faster because it uses
a fixed `n_flips` values when testing PickyFix. The script to run it is `bike/run_threshold.sh`. Using
`AVX2=1`, the test takes only a few minutes to run, considering level 1 parameters.

### Data to be reproduced

* `data/threshold/level1.csv`

This data file is used in Figure 4.

### Steps to reproduce

To minimize space, we put only the file for level 1, which is generated by.
```
$ mkdir -p reproduced/threshold/tmp1
$ ./run_threshold.sh reproduced/threshold/tmp1 1 10000 AVX512=1  # YOU MAY NEED TO ADJUST TO YOUR AVX SUPPORT
$ mv reproduced/threshold/tmp1/output1.csv > reproduced/threshold/level1.csv
```

However, we invite the reader to run the code below and see how the first threshold is
problematic also for levels 3 and 5.
```shell
$
for level in 1 3 5; do
    mkdir -p reproduced/threshold/tmp$level
    # YOU MAY NEED TO ADJUST TO YOUR AVX SUPPORT BELOW
    time ./run_threshold.sh reproduced/threshold/tmp$level $level 10000 AVX512=1
done
$ head -n 1 reproduced/threshold/tmp1/output1.csv > reproduced/threshold/header.csv
$ tail -q -n +2 reproduced/threshold/tmp1/output1.csv \
    reproduced/threshold/tmp3/output3.csv \
    reproduced/threshold/tmp5/output5.csv > reproduced/threshold/body.csv
$ cat reproduced/threshold/header.csv \
      reproduced/threshold/body.csv > reproduced/threshold/threshold.csv
```


## DFR

**IMPORTANT:** This is the hardest test to reproduce, as it requires a lot of computing power.
Considering our server with 2x Intel® XeonTM Gold 5118 CPU at 2.30GHz, running with 24 of
its 48 threads, this experiment using AVX512 instructions took roughly 75 hours.

The setup for this test is in file `data/setup/dfr_experiment.csv`. Let us consider its content

```
DECODER,LEVEL,MAX_IT_LIST,R_BITS,N_TESTS,EXPERIMENT_CMD,DFR_ESTIMATE
PickyFix,1,2,9001,10000,./bin/main,1.0
PickyFix,1,2,9101,10000,./bin/main,1.0
PickyFix,1,2,9201,10000,./bin/main,1.0
PickyFix,1,2,9301,10000,./bin/main,1.0
PickyFix,1,2,9401,10000,./bin/main,1.0
PickyFix,1,2,9501,100000,./bin/main,0.99955
PickyFix,1,2,9601,100000,./bin/main,0.98929
PickyFix,1,2,9701,100000,./bin/main,0.92285
PickyFix,1,2,9801,100000,./bin/main,0.69989
PickyFix,1,2,9901,100000,./bin/main,0.3564
PickyFix,1,2,10001,1000000,./bin/main,0.115497
PickyFix,1,2,10101,1000000,./bin/main,0.025546
PickyFix,1,2,10201,1000000,./bin/main,0.003832
PickyFix,1,2,10301,10000000,./bin/main,0.0004474
PickyFix,1,2,10351,10000000,./bin/main,0.0001448
...
```

Each line correspond to a DFR estimation using

- `DECODER`: The decoder to use
- `LEVEL`: The security level
- `MAX_IT_LIST`: The number of iterations to use for the decoder
- `R_BITS`: Parameter `R_BITS`
- `N_TESTS`: Number of tests for the DFR estimation
- `EXPERIMENT_CMD`: The command for the DFR estimation
- `DFR_ESTIMATE`: The DFR estimate that serves only as a guide when choosing parameters.

This test is so important that we wrote a `python` program to run this test: `analysis/dfr_experiment.py`

To run it, first we need to install its dependencies:
```
$ cd analysis
$ pipenv install
$ pipenv shell
```

Under the virtual environment, we can run the script help to see how to use it:
```
(analysis) $ ./dfr_experiment.py --help
usage: dfr_experiment.py [-h] [--AVX AVX] [--n_threads N_THREADS]
                         [--base_seed BASE_SEED] [--overwrite]
                         [--stop_if_ff_dfr_is_zero] bike_root experiment_csv working_dir

positional arguments:
  bike_root             path to root of BIKE implementation (where make should be run).
  experiment_csv        path to CSV file containing experiment parameters.
  working_dir           path to a non-existing directory that will be used for temporary files.

optional arguments:
  -h, --help            show this help message and exit
  --AVX AVX             Target AVX set to use: 2, 512 or leave empty if the portable implementation should be used.
  --n_threads N_THREADS
                        number of CPU threads to use. Default: use all.
  --base_seed BASE_SEED
                        seed used to generate other seeds for each run.
  --overwrite           flag to overwrite working directory
  --stop_if_ff_dfr_is_zero
                        flag to stop simulation when observed DFR is 0 for PickyFix

```

If you plan to use this experiment for real estimation, we highly recommend you run in a system with AVX512 support,
otherwise the test will take too much time.

In our system, we used the following command line:
```
(analysis) $ ./dfr_experiment.py --AVX=512 --n_threads=24 ../bike ../data/setup/dfr_experiment.csv dfr_out
```

This will create a report file `dfr_out/dfr_results.out` that should be equal to `data/dfr/dfr_all.csv` of the format:
```
decoder,n_iterations,level,error_weight,r_bits,n_failures,n_tests,dfr
PickyFix,2,1,134,9001,10000,10000,1.0
PickyFix,2,1,134,9101,10000,10000,1.0
PickyFix,2,1,134,9201,10000,10000,1.0
PickyFix,2,1,134,9301,10000,10000,1.0
PickyFix,2,1,134,9401,10000,10000,1.0
PickyFix,2,1,134,9501,99955,100000,0.99955
PickyFix,2,1,134,9601,98929,100000,0.98929
PickyFix,2,1,134,9701,92285,100000,0.92285
PickyFix,2,1,134,9801,69989,100000,0.69989
PickyFix,2,1,134,9901,35640,100000,0.3564
PickyFix,2,1,134,10001,115497,1000000,0.115497
PickyFix,2,1,134,10101,25546,1000000,0.025546
PickyFix,2,1,134,10201,3832,1000000,0.003832
PickyFix,2,1,134,10301,4474,10000000,0.0004474
PickyFix,2,1,134,10351,1448,10000000,0.0001448
...
```

### Data to be reproduced

* `data/dfr/dfr_all.csv`
    Used for Figure 8.
* `data/dfr/bgf_level1.csv`
    Used for Figure 3.


### Steps to reproduce

**IMPORTANT:** To reproduce exactly our data, you will have to use exactly the same number of threads (i.e. 24).
This is a consequence of the way we seed our different threads.


Go to directory `analysis` and start the Python virtual environment with `pipenv`. Then
```
$ mkdir -p reproduced/dfr
$ ./dfr_experiment.py --AVX=512 --n_threads=24 ../bike ../data/setup/dfr_experiment.csv reproduced/tmp_dfr
# THIS WILL TAKE A LONG TIME (~ 75 hours)
$ cp reproduced/tmp_dfr/dfr_results.out reproduced/dfr/dfr_all.csv
$
$ ./dfr_experiment.py --AVX=512 --n_threads=24 ../bike ../data/setup/dfr_experiment_bgf_level1_problem.csv reproduced/tmp_dfr_bgf
# THIS WILL TAKE A WHILE
$ cp reproduced/tmp_dfr_bgf/dfr_results.out reproduced/dfr/bgf_level1.csv
```

## Concavity

The concavity experiment is a simple variant of the DFR experiment but with an exaggerated error weight
and a lower number of tests (otherwise it would be too costly).

### Data to be reproduced

* `data/concavity/bgf_level1.csv`
    Used for Figure 5.
* `data/concavity/pf_level1.csv`
    Used for Figure 7.

### Steps to reproduce

**IMPORTANT:** To reproduce exactly our data, you will have to use exactly the same number of threads (i.e. 24 or 40).
This is a consequence of the way we seed our different threads.

Go to directory `analysis` and start the Python virtual environment with `pipenv` as detailed in the
previous section (DFR). Then
```
$ mkdir -p reproduced/concavity
$ ./dfr_experiment.py --AVX=512 --n_threads=24 ../bike ../data/setup/concavity_experiment_bgf_level1.csv reproduced/tmp_concavity_bgf
# THIS WILL TAKE A WHILE
$ cp reproduced/tmp_concavity_bgf/dfr_results.out reproduced/concavity/bgf_level1.csv
$ ./dfr_experiment.py --AVX=512 --n_threads=40 ../bike ../data/setup/concavity_experiment_pickyfix_level1.csv reproduced/tmp_concavity_pf
# THIS WILL TAKE A WHILE
$ cp reproduced/tmp_concavity_pf/dfr_results.out reproduced/concavity/pf_level1.csv
```

## Performance

We now show how we estimated the performance of the algorithm. This is the only result that
we expect you to see slightly different results than ours, because of the nature of this data.

### Data to be reproduced

* `data/performance/all.csv`

Used for Table 5.

### Steps to reproduce

In `bike` directory, run the shell script `./run_performance_test.sh` as below.

```shell
$ mkdir -p reproduced/performance
$ ./run_performance_test.sh | tee reproduced/performance/all.csv
implementation,decoder,level,n_iterations,r_bits,cycles
avx512,BGF,1,5,12323,1253180.96
avx512,BGF,3,5,24659,3935917.32
avx512,BGF,5,5,40973,10873523.10
portable,BGF,1,5,12323,10340596.80
portable,BGF,3,5,24659,31178523.46
portable,BGF,5,5,40973,89649927.98
avx512,PickyFix,1,2,13829,992199.80
avx512,PickyFix,1,3,13109,1096159.36
avx512,PickyFix,1,4,12739,1213229.36
avx512,PickyFix,1,5,12413,1341189.42
avx512,PickyFix,3,2,27397,2903644.84
avx512,PickyFix,3,3,25867,3241641.76
avx512,PickyFix,3,4,25189,3633758.88
avx512,PickyFix,3,5,24677,4046768.14
avx512,PickyFix,5,2,41411,7190184.46
avx512,PickyFix,5,3,39901,8228689.02
avx512,PickyFix,5,4,39163,9360594.18
avx512,PickyFix,5,5,39019,10544398.68
portable,PickyFix,1,2,13829,8581052.98
portable,PickyFix,1,3,13109,9612084.50
portable,PickyFix,1,4,12739,10861147.42
portable,PickyFix,1,5,12413,12170507.62
portable,PickyFix,3,2,27397,23751521.86
portable,PickyFix,3,3,25867,27262014.12
portable,PickyFix,3,4,25189,30673611.46
portable,PickyFix,3,5,24677,34596916.80
portable,PickyFix,5,2,41411,61683202.52
portable,PickyFix,5,3,39901,71916444.44
portable,PickyFix,5,4,39163,82147943.52
```

# Figures

The figures are generated by `analysis/plotters/plots.py`.

We believe that it is useful to make this file available as it can make it easier for researchers
trying to explore the data and find better parameters for PickyFix or even variants of BGF.

To use it, you'll need to activate the appropriate `pipenv` with:

```shell
$ cd analysis/plotters/
$ pipenv install
$ pipenv shell
$ ipython
Python 3.9.5 (default, May  4 2021, 03:36:27)
Type 'copyright', 'credits' or 'license' for more information
IPython 8.1.1 -- An enhanced Interactive Python. Type '?' for help.
````

Now, inside `ipython` we can generate all plots with a simple sequence of steps. The plots
will consider the data from the `data` directory.
```python
$
In [1]: run plots.py

In [2]: latexify_lncs()

In [3]: mkdir figures

In [4]: generate_all_plots('figures')

In [7]: ls figures/
bgf_threshold_problem.pdf  concavity_bgf_level1.pdf  counters_level5.pdf  dfr_extrapolation_level1.pdf
compare_n_errors.pdf       concavity_pf_level1.pdf   dfr_bgf_level1.pdf   pickyfix_dfr.pdf
```

Notice that these are the plots used in the paper.


# Exploring the PickyFix code


We suggest to start by opening file `pickyfix/pickyfix.c`. There, you will find
the `decode_pickyfix` function which implements PickyFix in a way such that one
can easily match steps in the corresponding `PickyFix` Algorithm in the paper.

```c
// Function: decode_pickyfix
// ------------------------
//
//  The full decoding of an error vector, given a ciphertext. This is the entry
//  point of the contribution of our paper.
//
//  We propose this algorithm as a replacement for BGF. The reader is invited
//  to inspect the code for decode_bgf in decode/decode.c to see the similarities
//  (and differences) between the two.
//
//  Notice that: for each security level, a different number of flips is made
//  in the first iteration. This is defined by the constant FIXFLIP_HEAD_N_FLIPS.
//  Furthermore, notice that the threshold used by bitflip_iter is the same
//  as the one used in BGF, but in FixFlip, they are used at different times.
//
// Input arguments:
//  - syndrome_t *original_s: The target syndrome
//  - ct_t *ct: The ciphertext
//  - sk_t *sk: The secret key
//
// Output arguments:
//  - sp
ret_t
decode_pickyfix(OUT split_e_t *e,
                IN const syndrome_t *original_s,
                IN const ct_t *ct,
                IN const sk_t *sk) {
    syndrome_t s;

    memset(e, 0, sizeof(*e));
    s = *original_s;
    dup(&s);

    for (int i = 0; i < MAX_IT; i++) {
        if (i == 0) {
            GUARD(fixflip_iter(e, &s, FIXFLIP_HEAD_N_FLIPS, ct, sk));
            GUARD(pickyflip_iter(e, &s, get_threshold(&s), (DV + 1) / 2, ct, sk));
            GUARD(pickyflip_iter(e, &s, get_threshold(&s), (DV + 1) / 2, ct, sk));
        } else {
            GUARD(pickyflip_iter(e, &s, get_threshold(&s), (DV + 1) / 2, ct, sk));
        }
    }
    if (r_bits_vector_weight((r_t *)s.qw) > 0) {
        DMSG("    Weight of e: %lu\n",
             r_bits_vector_weight(&e->val[0]) + r_bits_vector_weight(&e->val[1]));
        DMSG("    Weight of syndrome: %lu\n", r_bits_vector_weight((r_t *)s.qw));
        BIKE_ERROR(E_DECODING_FAILURE);
    }

    return SUCCESS;
}
```

Then, the reader is invited to explore the PickyFlip iteration in function `pickyflip_iter`
in the same file `pickyfix/pickyfix.c`. We suggest that the reader compares it with
the implementation of the auxiliary iteration for BGF, that can be found in
function `find_err1` from file `decode/decode.c:`. The reader will see that our implementation
of this function is completely based on the BGF implementation, and we even kept their original
comments.

```c
// Function: pickyflip_iter
// ----------------------
//
//  IMPORTANT NOTICE:
//  ================
//  TO IMPLEMENT pickyflip_iter, WE REUSED FUNCTION find_err1, ORIGINALLY IMPLEMENTED BY
//  Nir Drucker, Shay Gueron, and Dusan Kostic, AWS Cryptographic Algorithms Group.
//  (ndrucker@amazon.com, gueron@amazon.com, dkostic@amazon.com)
//  ===========================================================================
//
//
//  Flips `n_flips` bits of a partial error vector `e` inplace. Additionally, the syndrome is
//  recomputed for the new value of `e` and `syndrome` is updated.
//
// Input arguments:
//  - split e_t *e: The partial error vector up to this point.
//  - syndrome_t *syndrome: The syndrome
//  - uint8_t threshold_in: The UPC threshold for flipping a bit from 0 to 1
//  - uint8_t threshold_out: The UPC threshold for flipping a bit from 1 to 0
//  - ct_t *ct: The ciphertext (used to recomputed the syndrome after flipping bits of e)
//  - sk_t *sk: The secret key (used to recomputed the syndrome after flipping bits of e)
//
// Output arguments:
//  - split_e_t *e: The partial error vectors after the n_flips bits were flipped
//  - syndrome_t *syndrome: The recomputed syndrome for the new error vector `e`
//
ret_t
pickyflip_iter(OUT split_e_t *e,
               IN syndrome_t *  syndrome,
               IN const uint8_t threshold_in,
               IN const uint8_t threshold_out,
               IN const ct_t *ct,
               IN const sk_t *sk) {
    DEFER_CLEANUP(syndrome_t rotated_syndrome = {0}, syndrome_cleanup);
    DEFER_CLEANUP(upc_t upc, upc_cleanup);

    split_e_t e_copy;
    memcpy(&e_copy, e, sizeof(*e));

    assert(threshold_in >= threshold_out);

    for (uint32_t i = 0; i < N0; i++) {
        // UPC must start from zero at every iteration
        memset(&upc, 0, sizeof(upc));

        // 1) Right-rotate the syndrome for every secret key set bit index
        //    Then slice-add it to the UPC array.
        for (size_t j = 0; j < DV; j++) {
            rotate_right(&rotated_syndrome, syndrome, sk->wlist[i].val[j]);
            bit_sliced_adder(&upc, &rotated_syndrome, LOG2_MSB(j + 1));
        }

        // 2) Subtract the threshold from the UPC counters
        bit_slice_full_subtract(&upc, threshold_out); // threshold_in > threshold_out

        // 3) Update the errors vector.
        //    The last slice of the UPC array holds the MSB of the accumulated
        //    values minus the threshold. Every zero bit indicates a potential
        //    error bit.
        const r_t *last_slice_out = &(upc.slice[SLICES - 1].u.r.val);
        for (size_t j = 0; j < R_SIZE; j++) {
            const uint8_t sum_msb = (~last_slice_out->raw[j]);
            e->val[i].raw[j] ^= ((e_copy.val[i].raw[j]) & sum_msb);
        }
        e->val[i].raw[R_SIZE - 1] &= LAST_R_BYTE_MASK;

        // Now we have to consider the bits that are 0 to be flipped to 1.
        // This is controlled by theshold_in. Since upc was already
        // subtracted by threshold_out, we just need to subtract it by
        // (threshold_in - threshold_out)
        bit_slice_full_subtract(&upc, threshold_in - threshold_out);
        const r_t *last_slice_in = &(upc.slice[SLICES - 1].u.r.val);
        for (size_t j = 0; j < R_SIZE; j++) {
            const uint8_t sum_msb = (~last_slice_in->raw[j]);
            e->val[i].raw[j] ^= (~(e_copy.val[i].raw[j]) & sum_msb);
        }

        // Ensure that the padding bits (upper bits of the last byte) are zero so
        // they will not be included in the multiplication and in the hash
        // function.
        e->val[i].raw[R_SIZE - 1] &= LAST_R_BYTE_MASK;
    }

    GUARD(recompute_syndrome(syndrome, ct, sk, e));
    return SUCCESS;
}
```

Now, we invite you to explore the FixFlip iteration. This consists of a very simple looking function
`fixflip_iter` in file `pickyfix/pickyfix.c` that starts by computing the UPC in non-bitsliced
format `ff_upc`, and then calling the `flip_worst_fit_indexes` that flips the `n_flips` bits
of `e` that have the highest corresponding UPC values.
```c
// Function: fixflip_iter
// ----------------------
//
//  Flips `n_flips` bits of a partial error vector `e` inplace. Additionally, the syndrome is
//  recomputed for the new value of `e` and `syndrome` is updated.
//
// Input arguments:
//  - split e_t *e: The partial error vector up to this point.
//  - syndrome_t *syndrome: The syndrome
//  - uint32_t n_flips: The number of bits to be flipped
//  - ct_t *ct: The ciphertext (used to recomputed the syndrome after flipping bits of e)
//  - sk_t *sk: The secret key (used to recomputed the syndrome after flipping bits of e)
//
// Output arguments:
//  - split_e_t *e: The partial error vectors after the n_flips bits were flipped
//  - syndrome_t *syndrome: The recomputed syndrome for the new error vector `e`
//
ret_t
fixflip_iter(OUT split_e_t *e,
             OUT syndrome_t *  syndrome,
             IN const uint32_t n_flips,
             IN const ct_t *ct,
             IN const sk_t *sk) {

    fixflip_upc_t ff_upc;
    memset(&ff_upc, 0, sizeof(ff_upc));

    get_upc(&ff_upc, syndrome, sk->wlist);
    flip_worst_fit_indexes(e, &ff_upc, n_flips);

    GUARD(recompute_syndrome(syndrome, ct, sk, e));
    return SUCCESS;
}
```

As one can guess, the complexity of the implementation is behind the `flip_worst_fit_indexes` function,
that we will explore next. This function starts by obtaining the FixFlip threshold, which in the
paper consists of an UPC threshold `tau` and the number `n_tau` of UPC equal to `tau` that must
be flipped. In the implementation, this pair is managed by type `fixflip_threshold_t`.

Then it runs through the bits `2 * R_BITS` and flips them according to the FixFlip threshold.
This is done by the main `for` loop is just responsible for flipping bits based on their UPC values
with care not to flip more than `n_flips` bits (which, remember, is the main function of
having `n_tau` represented by `ff_threshold.n_equal_threshold`).

Below, we consider function `flip_worst_fit_indexes` from the portable implementation
in file `secure_pickyfix_portable.c`.

First consider the UNSAFE non-randomized variant. This is used for extrapolation purposes.
This function is unsafe because it has a bias towards flipping bits to the left of the error
vector, among those whose UPC are equal to the threshold tau.

```c
uint32_t
flip_worst_fit_indexes(OUT split_e_t *e, IN fixflip_upc_t *ff_upc, IN uint32_t n_flips) {
    uint32_t vals[DV + 1] = {0};

    fixflip_threshold_t ff_threshold = {0};
    get_fixflip_threshold(&ff_threshold, ff_upc, n_flips);

    uint8_t e_decomp[2 * R_BITS] = {0};
    decompress_e(e_decomp, e);

    // The two variables bellow count the number of UPC counters that are found to be
    // equal and greater than the FixFlip threshold computed by get_fixflip_threshold.
    uint32_t n_found_eq_thresh = 0;
    uint32_t n_found_gt_thresh = 0;
    // By the end of the loop, it is expected that:
    //      n_found_eq_thresh = ff_threshold.n_equal_threshold
    //      n_found_gt_thresh + n_found_eq_thresh = n_flips

    // Runs through all the 2*R_BITS UPC counters
    for (uint32_t i = 0; i < 2 * R_BITS; i++) {
        uint8_t counter = upc_for_index(ff_upc, i);

        // mask_gt assumes the following values:
        //      0 if the current counter is <= ff_threshold.threshold
        //      1 otherwise.
        uint32_t mask_gt = 1 + secure_l32_mask(ff_threshold.threshold, counter);
        n_found_gt_thresh += mask_gt;

        // mask_eq assumes the following values:
        //      0 if current counter is == ff_threshold.threshold AND if
        //           n_found_eq_thresh < ff_threshold.n_equal_threshold
        //      1 otherwise.
        // Therefore, it controls if the corresponding index `i` will be chosen to
        // flipped, when its counter is equal to the FixFlip threshold.
        //
        // Remember that this is done because we cannot flip all bits whose counter is equal
        // to the threshold, because we risk flipping more than n_flips bits.
        uint32_t mask_eq = secure_cmp32(counter, ff_threshold.threshold);
        mask_eq &= 1 + secure_l32_mask(n_found_eq_thresh, ff_threshold.n_equal_threshold);

        n_found_eq_thresh += mask_eq;
        e_decomp[i] ^= (mask_gt | mask_eq);
    }
    assert(n_found_eq_thresh == ff_threshold.n_equal_threshold);
    assert(n_found_gt_thresh == n_flips - ff_threshold.n_equal_threshold);

    compress_e(e, e_decomp);

    return ff_threshold.threshold;
}
```

Now compare it to the __SAFE randomized__ variant, which has no bias when flipping bits.
This should be used in real-world systems code and is used by default in our code
(except under the extrapolation framework).
Its usage is controlled by the default definition
`#define USE_RANDOMIZED_SELECTION_OF_EQ_THRESHOLD_BITS` in `bike/pickyfix/pickyfix.h`.

```c
uint32_t
flip_worst_fit_indexes(OUT split_e_t *e, IN fixflip_upc_t *ff_upc, IN uint32_t n_flips) {
    DEFER_CLEANUP(uint32_t vals[DV + 1] = {0}, vals_cleanup);

    fixflip_threshold_t ff_threshold = {0};
    get_fixflip_threshold(&ff_threshold, ff_upc, n_flips);

    uint8_t e_decomp[2 * R_BITS] = {0};
    decompress_e(e_decomp, e);

    uint32_t total_upc_counters_eq_threshold = ff_threshold.total_equal_threshold;
    uint64_t eq_flip_flags[N_FLIP_FLAGS_BLOCKS] = {0};
    init_eq_flip_flags(eq_flip_flags, &ff_threshold);
    secure_shuffle_eq_flip_flags(eq_flip_flags, &ff_threshold, total_upc_counters_eq_threshold);
    uint32_t current_eq_weight = 0;

    // The two variables bellow count the number of UPC counters that are found to be
    // equal and greater than the FixFlip threshold computed by get_fixflip_threshold.
    uint32_t n_found_eq_thresh = 0;
    uint32_t n_found_gt_thresh = 0;
    // By the end of the loop, it is expected that:
    //      n_found_eq_thresh = ff_threshold.n_equal_threshold
    //      n_found_gt_thresh + n_found_eq_thresh = n_flips

    uint32_t next_32_flags = 0;
    uint32_t base = 0;

    // Runs through all the 2*R_BITS UPC counters
    for (uint32_t i = 0; i < 2 * R_BITS; i++) {
        uint8_t counter = upc_for_index(ff_upc, i);

        // After each sequence of 32 bits is done, we have to update the next 32 flags of bits to flip.
        // Notice that, in general, not all 32 bits were consumed, and the variable current_eq_weight
        // ensures that we get the next 32 flags. Furthermore, notice that access to eq_flip_flags
        // are done in constant-time because we cannot leak current_eq_weight.
        if (i % 32 == 0) {
            next_32_flags = update_next32_flags(eq_flip_flags, current_eq_weight);
            base = 0;
        }
        // mask_gt assumes the following values:
        //      0 if the current counter is <= ff_threshold.threshold
        //      1 otherwise.
        uint32_t mask_gt = 1 + secure_l32_mask(ff_threshold.threshold, counter);
        n_found_gt_thresh += mask_gt;

        // mask_eq assumes the following values:
        //      0 if current counter is == ff_threshold.threshold AND if
        //           n_found_eq_thresh < ff_threshold.n_equal_threshold
        //      1 otherwise.
        // Therefore, it controls if the corresponding index `i` will be chosen to
        // flipped, when its counter is equal to the FixFlip threshold.
        //
        // Remember that this is done because we cannot flip all bits whose counter is equal
        // to the threshold, because we risk flipping more than n_flips bits.
        uint32_t mask_eq = secure_cmp32(counter, ff_threshold.threshold);


        uint64_t eq_flip_mask = get_randomized_eq_flip_mask(next_32_flags,
                                                            &base,
                                                            &current_eq_weight,
                                                            mask_eq);

        n_found_eq_thresh += eq_flip_mask;
        e_decomp[i] ^= (mask_gt | eq_flip_mask);
    }
    assert(n_found_eq_thresh == ff_threshold.n_equal_threshold);
    assert(n_found_gt_thresh == n_flips - ff_threshold.n_equal_threshold);

    compress_e(e, e_decomp);

    return ff_threshold.threshold;
}
```

Again, most of the complexity is behind another function. This time, let us expand `get_fixflip_threshold`
from the portable implementation in `pickyfix/pickyfix.c`. This is where the main part of FixFlip's
implementation occurs: the sequence of `COUNTING_LEVELS = 3` partial counting steps to find the
FixFlip threshold. For clarity, we used two auxiliary functions: `reduce_upcs_then_count` and `find_threshold_bucket`.
The first one simply reduces the UPC counters, that is, it defines what is the corresponding bucket for each UPC counter,
and then count it to the adequate bucket. The second one, `find_threshold_bucket`, is to find out which threshold bucket
should be expanded in the next step, that is, it finds out in which bucket the FixFlip threshold lives.

```c
// Function:  get_fixflip_threshold
// --------------------------------
//
// Finds the FixFlip threshold data used by fixflip_iter to flip a fixed number (n_flips) of bits.
// Remember that the FixFlip threshold data is defined not only by a threshold number, but by a
// pair: (tau, n_tau), which, in this implementation is represented by the type
// fixflip_threshold_t defined in fixflip.h as follows:
//      typedef struct fixflip_threshold_s {
//          uint8_t  threshold;                     // Represents threshold tau
//          uint8_t  n_equal_threshold;             // Represents n_tau
//      } fixflip_threshold_t;
//
//  Function fixflip_iter then flips n_flips bits doing the following:
//      - If the bit UPC counter is greater than `threshold`: flip the bit
//      - Flip only `n_equal_threshold` bits whose UPC counter is equal `threshold`
//
// Input Arguments:
//  - fixflip_upc_t *ff_upc: The UPC counter values
//  - uint32_t       n_flips: The number of bits to be flipped
//
// Output Argument:
//  - fixflip_threshold_t *ff_threshold: The fixflip threshold data to be used by fixflip_iter
//                                       when deciding which bits to flip.
//
//  Implementation:
//      This function performs COUNTING_LEVELS = 3 rounds of countings to find the threshold
//      values. In each level, the resolution of the counting buckets the search gets smaller. In
//      the first iteration each bucket represents a range of numbers, and by the last iteration
//      buckets represents only one number. The idea is that each iteration decides in which
//      bucket the threshold lives, and this bucket is expanded in the next iteration.
//
void
get_fixflip_threshold(OUT fixflip_threshold_t *ff_threshold,
                      IN fixflip_upc_t *ff_upc,
                      IN uint32_t       n_flips) {

    uint32_t base = 0;

    ff_threshold->threshold         = 0;
    ff_threshold->n_equal_threshold = 0;

    // This variable counts the number of elements in buckets that are greater than
    // the current threshold_bucket
    uint32_t n_gt_threshold = 0;

    // As described in the paper, the search for the threshold is done in COUNTING_LEVELS =
    // iterations. In each iteration, the algorithm expands the bucket of reduced counters where
    // the threshold should be in.
    for (int i = 0; i < COUNTING_LEVELS; i++) {

        uint8_t counts[COUNTING_SORT_BUCKETS] = {0};

        // The step size resolution is increased in each iteration, which narrows down the value
        // of the fixflip threshold.
        //
        // In particular, step = 8 ^ (COUNTING_LEVELS - 1 - i)
        //
        // That is:
        //      - when i = 0: step = 64
        //      - when i = 1: step = 8
        //      - when i = 2: step = 1

        uint32_t step = 1 << (3 * (COUNTING_LEVELS - 1 - i));

        // Get the reduced counters counted into the following 8 UPC buckets
        // Bucket 0: [base, base + step[
        // Bucket 1: [base + step, base + 2*step[
        //  ...,
        // Bucket 7: [base + 7*step, base + 8*step[
        reduce_upcs_then_count(counts, ff_upc, base, step);

        // Find out which of the 8 buckets above contains the threshold tau
        uint8_t threshold_bucket = 0;
        find_threshold_bucket(&threshold_bucket, &n_gt_threshold, counts, n_flips);

        // Move base to the start of the bucket where the threshold lives
        base += threshold_bucket * step;
    }
    ff_threshold->threshold         = base;
    ff_threshold->n_equal_threshold = n_flips - n_gt_threshold;
}
```

# Conclusion

We invite everyone interested in BIKE to experiment with our code and try to find better parameters and
decoding procedures.
