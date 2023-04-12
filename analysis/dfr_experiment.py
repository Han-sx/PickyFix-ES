#!/usr/bin/env python3

import argparse
import hashlib
import multiprocessing
import os
import random
import shutil
import sys
import subprocess
import threading

import numpy as np
import pandas as pd
import tqdm


AVX_TO_MAKE_OPTION = {
    None: '',
    '': '',
    '2': 'AVX2=1',
    '512': 'AVX512=1',
}


class Experiment():

    def __init__(self, experiment_cmd, decoder, n_tests, max_it: int, level: int, r_bits: int, avx: str=None, base_seed: int=0,
                 bike_root='.', error_weight=None, time_it=None):

        self.experiment_cmd = experiment_cmd
        self.decoder = decoder
        self.n_tests = n_tests
        self.max_it = max_it
        self.r_bits = r_bits
        self.level = level
        self.avx = avx
        self.base_seed = base_seed
        self.bike_root = bike_root
        self.error_weight = error_weight
        self.time_it = time_it

        self.binary_hash = None

    def get_make_cmd(self):

        dec_option = ''
        if self.decoder == 'BGF':
            dec_option = 'TEST_BGF=1'
        elif self.decoder == 'PickyFix':
            dec_option = 'TEST_PICKYFIX=1'
        elif self.decoder == 'BOTH':
            dec_option = 'TEST_BGF=1 TEST_PICKYFIX=1'

        command_line = [
            f'make',
            f'CC=gcc',
            f'R_BITS={self.r_bits}',
            f'MAX_IT={self.max_it}',
            f'LEVEL={self.level}',
            f'{dec_option}',
        ]

        if not args.randomized_selection_of_eq_threshold_bits:
            command_line.append('USE_UNSAFE_CODE_FOR_EXTRAPOLATION=1')

        if AVX_TO_MAKE_OPTION[self.avx]:
            command_line.append(f'{AVX_TO_MAKE_OPTION[self.avx]}')

        if self.error_weight:
            command_line.append(f'T1={self.error_weight}')

        if self.time_it:
            command_line.append('RDTSC=1')

        return command_line

    def get_experiment_seed_256_bits(self):
        exp_str = (f'{self.n_tests},'
                   f'{self.max_it},'
                   f'{self.r_bits},'
                   f'{self.level},'
                   f'{self.avx},'
                   f'{self.decoder},'
                   f'{self.base_seed}'
                   f'{self.error_weight}')

        hash = hashlib.sha256(exp_str.encode()).hexdigest()

        return int(hash, 16)

    def make_fresh_binary(self, output_file=None):
        if output_file is None:
            output = sys.stdout
        else:
            output = open(output_file, 'w')

        subprocess.run(['make', 'clean'], check=True, cwd=self.bike_root, stdout=output)
        subprocess.run(self.get_make_cmd(), check=True, cwd=self.bike_root, stdout=output)

        print('Successful in making object: %s' % ' '.join(self.get_make_cmd()))

        if output_file is not None:
            output.close()
        # TODO compute hash of binary to check that it has not changed.
        # self.binary_hash = ...

    def get_stdout_thread_fpath(self, base_dir_for_outputs, thread_id):
        return os.path.join(base_dir_for_outputs, f'{thread_id}.out.tmp')

    def get_stderr_thread_fpath(self, base_dir_for_outputs, thread_id):
        return os.path.join(base_dir_for_outputs, f'{thread_id}.err.tmp')

    def run_thread(self, thread_id, thread_seed, thread_n_tests, base_dir_for_outputs):
        print(f'{thread_id}...', end='')

        print(' '.join([self.experiment_cmd, f'{thread_n_tests}', f'{thread_seed}', '1', str(self.time_it)]))


        err_fname = self.get_stderr_thread_fpath(base_dir_for_outputs, thread_id)
        out_fname = self.get_stdout_thread_fpath(base_dir_for_outputs, thread_id)

        with open(err_fname, 'w') as err_file, open(out_fname, 'w') as out_file:

            subprocess.run([self.experiment_cmd, f'{thread_n_tests}', f'{thread_seed}', '1', str(self.time_it)],
                           check=True, cwd=self.bike_root, stdout=out_file, stderr=err_file)

    def write_experiment_info_file(self, base_dir_for_outputs, n_threads):
        with open(os.path.join(base_dir_for_outputs, 'info.dat'), 'w') as info_file:
            print(f'n_tests={self.n_tests}', file=info_file)
            print(f'max_it={self.max_it}', file=info_file)
            print(f'r_bits={self.r_bits}', file=info_file)
            print(f'error_weight={self.error_weight}', file=info_file)
            print(f'level={self.level}', file=info_file)
            print(f'avx={self.avx}', file=info_file)
            print(f'base_seed={self.base_seed}', file=info_file)
            print(f'bike_root={self.bike_root}', file=info_file)
            print(f'{n_threads=}', file=info_file)
            print(f'make_cmd={self.get_make_cmd()}', file=info_file)
            print(f'experiment_seed={self.get_experiment_seed_256_bits()}', file=info_file)
            print(f'thread_seeds={self.get_thread_seeds(n_threads)}', file=info_file)
            print(f'git_revision_hash={self.get_git_revision_hash()}', file=info_file)

    # Taken from https://stackoverflow.com/a/21901260
    def get_git_revision_hash(self):
        return subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=self.bike_root).decode('ascii').strip()

    def get_thread_seeds(self, n_threads):
        random.seed(self.get_experiment_seed_256_bits())
        return [random.randrange(1 << 32) for _ in range(n_threads)]

    def get_merged_dfr_from_threads_outputs(self, base_dir_for_outputs, n_threads):
        df = pd.read_csv(self.get_stdout_thread_fpath(base_dir_for_outputs, 0))
        for i in range(1, n_threads):
            tmp_df = pd.read_csv(self.get_stdout_thread_fpath(base_dir_for_outputs, i))
            df = df.append(tmp_df, ignore_index=True)

        merged_dfr = df.groupby(['decoder', 'n_iterations', 'level', 'error_weight', 'r_bits'], as_index=False) \
                      .agg({'n_failures': 'sum', 'n_tests': 'sum'})

        assert(all(merged_dfr.n_tests == self.n_tests))

        return merged_dfr

    def run(self, n_threads, base_dir_for_outputs):

        if os.path.exists(base_dir_for_outputs):
            raise ValueError(f'{base_dir_for_outputs=} already exists!')

        os.mkdir(base_dir_for_outputs)
        self.make_fresh_binary(os.path.join(base_dir_for_outputs, 'make.out'))

        self.write_experiment_info_file(base_dir_for_outputs, n_threads)

        thread_seeds = self.get_thread_seeds(n_threads)
        thread_n_tests = [self.n_tests // n_threads for _ in range(n_threads)]
        thread_n_tests[-1] += self.n_tests % n_threads

        threads = [threading.Thread(target=self.run_thread, args=(i, seed, n_tests, base_dir_for_outputs))
                   for (i, seed, n_tests) in zip(range(n_threads), thread_seeds, thread_n_tests)]

        for i, thread in enumerate(threads):
            if thread_n_tests[i] > 0:
                thread.start()

        for thread in threads:
            thread.join()

        print()

        dfr_df = self.get_merged_dfr_from_threads_outputs(base_dir_for_outputs, n_threads)
        dfr_df['dfr'] = dfr_df['n_failures'] / dfr_df['n_tests']

        dfr_df.to_csv(os.path.join(base_dir_for_outputs, 'dfr.out'), index=False)

        return dfr_df

def run_full_experiment(args):
    if (os.path.exists(args.working_dir) and not args.overwrite):
        print(f'Working directory parameters {args.working_dir} already exists.', file=sys.stderr)
        sys.exit(1)

    try:
        os.mkdir(args.working_dir)
    except FileExistsError:
        print(f'Overwriting working directory {args.working_dir}', file=sys.stderr)

    max_it_list_converter = lambda x: list(map(int, x.strip('[]').split()))
    exp_df = pd.read_csv(args.experiment_csv, comment='#', converters={'MAX_IT_LIST': max_it_list_converter})

    results_df = pd.DataFrame()

    shutil.copy(src=os.path.join(args.bike_root, 'pickyfix', 'pickyfix.c'),
                dst=os.path.join(args.working_dir, 'pickyfix.bak.c'))

    shutil.copy(src=args.experiment_csv,
                dst=os.path.join(args.working_dir, 'experiment.bak.csv'))

    dfr_is_zero = False
    for i, row in tqdm.tqdm(exp_df.iterrows(), total=len(exp_df)):

        for max_it in row.MAX_IT_LIST:
            error_weight = None if 'ERROR_WEIGHT' not in row else row.ERROR_WEIGHT
            time_it = None if 'TIME_IT' not in row else row.TIME_IT

            e = Experiment(experiment_cmd=row.EXPERIMENT_CMD,
                           max_it=max_it,
                           decoder=row.DECODER,
                           n_tests=row.N_TESTS,
                           level=row.LEVEL,
                           r_bits=row.R_BITS,
                           error_weight=error_weight,
                           time_it=time_it,
                           avx=args.AVX,
                           bike_root=args.bike_root,
                           base_seed=args.base_seed)

            terms = row.drop(['LEVEL', 'EXPERIMENT_CMD', 'MAX_IT_LIST'])
            # terms = row.drop(['LEVEL', 'EXPERIMENT_CMD', 'MAX_IT_LIST', 'estimated_dfr'])
            base_dir_for_outputs = '_'.join(map(str, terms))
            base_dir_for_outputs = f'LEVEL{row.LEVEL}_MAX_IT{max_it}_' + base_dir_for_outputs

            row_str = ' '.join([f'{a}={b}' for a, b in row.to_dict().items()])

            print('Parameters: ' + row_str)
            df = e.run(n_threads=args.n_threads, base_dir_for_outputs=os.path.join(args.working_dir, base_dir_for_outputs))
            print(df)
            print('==================================================================================')
            print()

            results_df = results_df.append(df, ignore_index=True)
            results_df.to_csv(os.path.join(args.working_dir, 'dfr_results.out'), index=False)

            if args.stop_if_ff_dfr_is_zero:
                if results_df[results_df.decoder == 'PickyFix'].iloc[-1].n_failures == 0:
                    print('Found DFR = 0 for PickyFix. Stopping...')
                    dfr_is_zero = True
                    break
        if dfr_is_zero:
            break



    print(results_df)
    results_df.to_csv(os.path.join(args.working_dir, 'dfr_results.out'), index=False)

    return results_df


def extrapolate_r(df, decoder, error_rate):
    r0, dfr0 = df[df.decoder == decoder].iloc[-2][['r_bits', 'dfr']]
    r1, dfr1 = df[df.decoder == decoder].iloc[-1][['r_bits', 'dfr']]

    log_dfr0 = np.log2(dfr0)
    log_dfr1 = np.log2(dfr1)
    log_error_rate = np.log2(error_rate)

    alpha = (log_dfr0 - log_dfr1) / (r0 - r1)

    return (log_error_rate + alpha*r1 - log_dfr1) / alpha


def extrapolate_r_vals(r0_dfr0, r1_dfr1, error_rate):

    r0, dfr0 = r0_dfr0
    r1, dfr1 = r1_dfr1

    log_dfr0 = np.log2(dfr0)
    log_dfr1 = np.log2(dfr1)
    log_error_rate = np.log2(error_rate)

    alpha = (log_dfr0 - log_dfr1) / (r0 - r1)

    return (log_error_rate + alpha*r1 - log_dfr1) / alpha


if __name__ == "__main__":

    parser = argparse.ArgumentParser()
    parser.add_argument('bike_root', help='path to root of BIKE implementation (where make should be run).')
    parser.add_argument('experiment_csv', help='path to CSV file containing experiment parameters.')
    parser.add_argument('working_dir', help='path to a non-existing directory that will be used for temporary files.')
    parser.add_argument('--AVX', help='Target AVX set to use: 2, 512 or leave empty if the portable implementation '
                                      'should be used.', default='')
    parser.add_argument('--n_threads', type=int, help='number of CPU threads to use. Default: use all.', default=multiprocessing.cpu_count())
    parser.add_argument('--base_seed', type=int, help='seed used to generate other seeds for each run.', default=0)
    parser.add_argument('--overwrite', action='store_true', default=False,
                        help='flag to overwrite working directory')

    parser.add_argument('--stop_if_ff_dfr_is_zero', action='store_true', default=False,
                        help='flag to stop simulation when observed DFR is 0 for PickyFix')

    parser.add_argument('--randomized_selection_of_eq_threshold_bits', action='store_true', default=False,
                        help='flag to use the safe (randomized) algorithm for extrapolation - not recommended')

    args = parser.parse_args()

    run_full_experiment(args)
