import matplotlib.pyplot as plt
import numpy as np
import pandas as pd
import seaborn as sns

import os
import pickle

from scipy import interpolate
from matplotlib import rc
from matplotlib import rcParams
from sympy import nextprime, is_primitive_root

from statsmodels.stats.proportion import proportion_confint


LNCS_FIG_WIDTH = 5.5
LNCS_BIG_FIG_HEIGHT = 5.5
LNCS_SMALL_FIG_HEIGHT = 2.5

#LNCS text width: 5.37502in


def latexify_lncs(fig_width=LNCS_FIG_WIDTH, fig_height=LNCS_SMALL_FIG_HEIGHT, small=False, fs=10):

    sns.reset_orig()

    rc('font', **{'family': 'serif', 'serif': ['Computer Modern']})
    rc('text', usetex=True)
    rcParams['font.size'] = fs
    from math import sqrt

    if fig_width is None:
        fig_width = 4.8  # approx 12.2 cm

    if fig_height is None:
        golden_mean = (sqrt(5) - 1.0) / 2.0  # Aesthetic ratio
        fig_height = fig_width * golden_mean  # height in inches

    MAX_HEIGHT_INCHES = 8.0
    if fig_height > MAX_HEIGHT_INCHES:
        print("WARNING: fig_height too large:" + fig_height +
              "so will reduce to" + MAX_HEIGHT_INCHES + "inches.")
        fig_height = MAX_HEIGHT_INCHES

    ticksize = fs
    if small:
        ticksize = 7

    params = {
        'backend': 'pdf',
        'axes.labelsize': fs,  # fontsize for x and y labels (was 10)
        'axes.titlesize': fs,
        'font.size': fs,  # was 10
        'legend.fontsize': fs,  # was 10
        'font.family': 'serif',
        'xtick.labelsize': ticksize,
        'ytick.labelsize': ticksize,
        'ytick.major.width': 0.3,
        'ytick.minor.width': 0.3,
        'xtick.major.width': 0.3,
        'xtick.minor.width': 0.3,
        'text.usetex': True,
        'legend.edgecolor': 'black',
        'legend.frameon': False,
        'axes.linewidth': 0.3,
        'axes.linewidth': 0.3,
        'figure.figsize': [fig_width, fig_height],
    }

    rcParams.update(params)


# plt.savefig('../figures/dfr_bgf_level1.pdf')
def plot_dfr_bgf_level1(datafile='../../data/dfr/bgf_level1.csv'):

    df = pd.read_csv(datafile)
    df = df[df.n_failures > 50]

    fig, ax = plt.subplots(1, figsize=(LNCS_FIG_WIDTH, LNCS_SMALL_FIG_HEIGHT))

    markers = ['|', 'v', 's', 'p']
    for i, n_iterations in enumerate([2, 3, 4, 5]):
        ax = sns.lineplot(data=df[df.n_iterations == n_iterations], x='r_bits', y='dfr', marker=markers[i],
                          lw=0.3, ms=2, color='black', ls='-', markeredgecolor='black', label=f'{n_iterations}', ax=ax)


    ax.set_yscale('log', base=2)


    ax.set_xlabel(r'Parameter $r$')
    ax.set_ylabel(r'Decryption Failure Rate')

    ax.set_xlim((9500, 10601))
    ax.set_ylim((2**(-15.5), 2))
    ax.legend(title='Iterations')
    ax.xaxis.set_tick_params(width=0.5)
    ax.yaxis.set_tick_params(width=0.5)

    sns.despine()
    plt.tight_layout()

    return ax

# plt.savefig('../figures/dfr_extrapolation_level1.pdf')
def plot_dfr_extrapolation_method():

    nodes = np.array([
        [9501, 0],
        [9601, np.log2(0.741552)],
        [9701, np.log2(0.333712)],
        [9801, np.log2(0.060556)],
        # [9901, np.log2(0.004568)],
        # [10001, np.log2(0.000202)],
        # [10051, np.log2(0.000040)],
        [11000, -135],
        [11500, -175],
        [12000, -193],
        [12100, -194],
        [12200, -195],
        [12400, -196],
    ])

    x = nodes[:,0]
    y = nodes[:,1]

    tck, u = interpolate.splprep([x, y], s=0)
    xnew, ynew = interpolate.splev(np.linspace(0, 1, 100), tck, der=0)

    simulation_points = [p for p in zip(xnew, ynew) if p[1] > -30]
    simx, simy = zip(*simulation_points[::2])

    fig, ax = plt.subplots(1)

    sns.lineplot(simx, simy, lw=0, color='black', marker='.',
                      label='DFR from simulations', ax=ax)
    sns.lineplot(xnew, ynew, lw=0.3, color='black', label='Real DFR', ax=ax)

    xa, xb = simx[-2:]
    ya, yb = simy[-2:]

    alpha = (yb - ya)/(xb - xa)
    xc = 20000
    yc = alpha*(xc - xa) + ya

    # print(xa, xc, ya, yc)
    ax.plot([xa, xc], [ya, yc], lw=0.5, ls='--', color='0.4', label='Extrapolated DFR')

    r_ext = xa + (-128 - ya)/alpha

    sns.lineplot([r_ext], [-128], color='black', marker='*', ms=10, ax=ax)


    ax.vlines(r_ext, -250, -128, color='black', lw=0.3, ls='dotted')

    ax.hlines(-128, 0, r_ext, color='black', lw=0.3, ls='dotted')

    ax.text(9550, -124, r'$\textrm{DFR} = 2^{-128}$')
    ax.text(r_ext + 50, -210, r'$r_\textrm{ext} = %d$' % int(r_ext))

    ylim_min = -220
    ax.set_xlim((9500, 12400))
    ax.set_ylim((ylim_min, 1))
    # ax.set_yscale('log', base=2)

    ax.set_xlabel(r'Parameter $r$')
    ax.set_ylabel(r'$\log_2(\textrm{DFR})$')

    arrowprops = dict(arrowstyle='->',
                      lw=0.3,
                      connectionstyle='angle,angleA=0,angleB=-90,rad=0.0')

    ax.annotate(rf'$(r_A, p_A)$',
            xy=(xa, ya), xycoords='data',
            xytext=(25, 16), textcoords='offset points',
            arrowprops=arrowprops,
            )

    ax.annotate(rf'$(r_B, p_B)$',
            xy=(xb, yb), xycoords='data',
            xytext=(18, 8), textcoords='offset points',
            arrowprops=arrowprops,
            )

    sns.despine()

    plt.tight_layout()
    plt.legend()

    return ax


def extrapolate_r(dfr_datafile='../../data/dfr/level5.csv', decoder='FixFlip', security_level=256):
    from sympy import nextprime

    df = pd.read_csv(dfr_datafile)

    r0, dfr0 = df[df.decoder == decoder].iloc[-2][['r_bits', 'dfr']]
    r1, dfr1 = df[df.decoder == decoder].iloc[-1][['r_bits', 'dfr']]

    log_dfr0 = np.log2(dfr0)
    log_dfr1 = np.log2(dfr1)

    log_error_rate = -security_level  # = log2(2**security_level)

    alpha = (log_dfr0 - log_dfr1) / (r0 - r1)

    return nextprime((log_error_rate + alpha*r1 - log_dfr1) / alpha)


def relative_change_percent(new, old, decimals=2):

    return np.round((new - old) / old * 100, decimals=decimals)


# plt.savefig('../figures/counters_level5.pdf')
def plot_counters(datafile='../../data/counters/counters_level5.csv'):

    df = pd.read_csv(datafile, comment='#')
    df = df[df.test == 0]

    fig, ax = plt.subplots(1) #, figsize=(IEEE_COL_WIDTH, 2))

    df.counter -= 0.5
    sns.histplot(data=df[df.n_right > 0], x='counter', weights='n_right', binwidth=1, color='0.7',
                 label='Correct bit', element='step', ax=ax)
    sns.histplot(data=df[df.n_wrong > 0], x='counter', weights='n_wrong', binwidth=1, color='0.4',
                 label='Incorrect bit', element='step', ax=ax)

    arrowprops = dict(arrowstyle='->',
                      lw=0.3,
                      connectionstyle='angle,angleA=0,angleB=-90,rad=0.0')
    ax.annotate("UPC = 76",
                xy=(76, 28), xycoords='data',
                xytext=(30, 10), textcoords='offset points',
                arrowprops=arrowprops,
                )
    ax.annotate("UPC = 77",
                xy=(77, 15), xycoords='data',
                xytext=(25, 33), textcoords='offset points',
                arrowprops=arrowprops,
                )

    # plt.xticks(range(10, 56, 5))
    plt.ylim(0, 50)
    ax.set_xlabel( r'UPC counter')
    ax.set_ylabel(r'Number of occurrences')

    plt.legend()

    sns.despine()
    plt.tight_layout()

    return ax


def get_radix_sort_example_data(datafile='../../data/counters/counters_level5.csv'):
    df = pd.read_csv(datafile)
    df = df[df.test == 0]
    df['n_both'] = df.n_right + df.n_wrong

    upc = df.n_both.to_list()

    nflips = 40
    base = 0
    nsorts = 3
    buckets = []
    factor = 8 ** (nsorts - 1)
    for i in range(3):
        print(i)
        buckets.append([0] * 8)

        for u, v in enumerate(upc):
            if u < base or u >= base + 8*factor:
                continue

            index = int((u - base) // factor)
            buckets[i][index] += v

        for j, v in enumerate(buckets[i]):
            buckets[i][j] = min(255, v)

        print(buckets[i])
        sum_counts = 0
        for i, v in enumerate(reversed(buckets[i])):
            sum_counts += v
            if sum_counts >= nflips:
                base = base + (7 - i)*factor
                break

        factor /= 8

        print(f'new {base=}')
        print(f'new {factor=}')

    return buckets


def baseround(x, base=5):
    return base * round(x/base)


# plt.savefig('../figures/compare_n_errors.pdf')
def plot_compare_n_errors(datafile='../../data/compare_n_errors/n_errors.csv'):

    df_all = pd.read_csv(datafile)

    fig, axs = plt.subplots(3, 1, figsize=(LNCS_FIG_WIDTH, LNCS_BIG_FIG_HEIGHT))

    bests = find_best_n_flips(datafile)
    # for i_ax, level in enumerate([1, 3, 5]):
    for i_ax, level in enumerate([1, 3, 5]):
        ax = axs[i_ax]
        df = df_all[df_all.LEVEL == level]

        sns.lineplot(data=df[df.decoder == 'BGF'], x='R_BITS', y='av_errors_left', ax=ax,
                     label=r'BGF\textsubscript{1}', lw=0.5, color='0')

        line_styles = ['dotted', 'dashed', 'dashdot']

        tgt_nflips = bests[level].nflips

        nflips_to_show = [baseround(tgt_nflips//2), tgt_nflips, baseround(tgt_nflips//2*3)]
        # nflips_to_show = [tgt_nflips - 10, tgt_nflips, tgt_nflips + 10]

        for i, nflips in enumerate(nflips_to_show):

            sns.lineplot(data=df[df.nflips == nflips], x='R_BITS', y='av_errors_left', ax=ax,
                         label=r'$\textrm{PickyFix}_1^{%d}$' % nflips, lw=0.5, color='0', ls=line_styles[i])

        ax.set_title(f'Level {level}', y=1)

        ax.legend(loc='upper right', fontsize=9)



        if i == 2:
            ax.set_xlabel(r'Parameter $r$')

        ax.set_ylabel(r'Errors left')

        sns.despine()

    axs[0].set_xlim((9600, 11000))
    axs[0].set_ylim((0, 300))
    axs[1].set_xlim((19200, 21000))
    axs[1].set_ylim((0, 500))
    axs[2].set_xlim((33200, 35000))
    axs[2].set_ylim((0, 600))

    plt.tight_layout()

    return axs



# plt.savefig("../figures/bgf_threshold_problem.pdf")
def plot_threshold_problem(datafile='../../data/threshold/level1.csv'):

    df_all = pd.read_csv(datafile, converters={'thresholds': lambda x: list(map(int, x.split()))})
    df_all = df_all[df_all.decoder == 'BGF']

    n_thresholds = len(df_all.thresholds.iloc[0])
    for i in range(n_thresholds):
        df_all[f'th{i}'] = df_all.thresholds.apply(lambda x: x[i])


    df = df_all.groupby(['LEVEL', 'R_BITS', 'T1', 'decoder'])[[f'th{i}' for i in range(n_thresholds)]].mean()
    fig, ax = plt.subplots(1)

    # markers = ['*', '|', 'v', 's', 'p']
    # msizes = [5, 5, 3, 3, 3]
    line_styles = ['-', '--', '-.', ':', (3, (20, 10))]
    for i, nflips in enumerate(range(n_thresholds)):
        sns.lineplot(data=df, x='R_BITS', y=f'th{i}', ax=ax,
                     label=f'{i + 1}', lw=0.5, color='0', #marker=markers[i],
                     ls=line_styles[i])
                     # ms=msizes[i], markeredgecolor='black')#, ls=line_styles[i])

    ax.legend(title='Iteration', loc='center right')

    ax.set_xlim((9000, 13000))

    ax.set_xlabel(r'Parameter $r$')
    ax.set_ylabel(r'Threshold $\tau_0$')

    sns.despine()

    plt.tight_layout()

    return ax


def extrapolate_r_worst(df, error_rate, ci_error=0.01):
    r0, dfr0 = df.iloc[-2][['r_bits', 'dfr']]
    r1, dfr1 = df.iloc[-1][['r_bits', 'dfr']]
    row0 = df.iloc[-2]
    row1 = df.iloc[-1]

    lower_dfr0, upper_dfr0 = proportion_confint(row0.n_failures, row0.n_tests, ci_error, method='beta')
    lower_dfr1, upper_dfr1 = proportion_confint(row1.n_failures, row1.n_tests, ci_error, method='beta')

    log_dfr0 = np.log2(lower_dfr0)
    log_dfr1 = np.log2(upper_dfr1)


    log_error_rate = np.log2(error_rate)

    alpha = (log_dfr0 - log_dfr1) / (r0 - r1)

    r_ext = (log_error_rate + alpha*r1 - log_dfr1) / alpha

    candidate_r = nextprime(r_ext)
    while not is_primitive_root(2, candidate_r):
        candidate_r = nextprime(candidate_r + 1)

    return candidate_r


def extrapolate_all_last(df, alpha=0.01, min_nfailures=1000):
    df = df.sort_values(['level', 'n_iterations'])
    df['dec_id'] = df.decoder + df.n_iterations.astype(str) + '_Level' + df.level.astype(str)

    sec_per_level = {
        1: 128,
        3: 192,
        5: 256,
    }

    for dec_id in df.dec_id.unique():
        dfx = df[(df.dec_id == dec_id) & (df.n_failures > min_nfailures)].sort_values(['r_bits'])

        sec = sec_per_level[dfx.iloc[0].level]

        i = len(dfx)
        i, r_ext = (i, extrapolate_r_worst(dfx[:i], 2**(-sec), ci_error=alpha))

        point1 = dfx.iloc[i - 2].r_bits, round(np.log2(dfx.iloc[i - 2].dfr), 2)
        point2 = dfx.iloc[i - 1].r_bits, round(np.log2(dfx.iloc[i - 1].dfr), 2)

        print(f'{dec_id} & ({point1[0]}, 2^{{{point1[1]}}}) & ({point2[0]}, 2^{{{point2[1]}}}) & {r_ext}')


def find_best_n_flips(datafile='../../data/compare_n_errors/n_errors.csv'):

    full_df = pd.read_csv(datafile)
    bgf_df = full_df[full_df.decoder == 'BGF']


    best = {}

    for level in [1, 3, 5]:

        df = full_df[(full_df.decoder == 'PickyFix') & (full_df.LEVEL == level)].sort_values('R_BITS')
        T1 = df.iloc[0].T1

        for r_bits in sorted(full_df[full_df.LEVEL == level].R_BITS.unique()):

            df = full_df[(full_df.decoder == 'PickyFix') &
                         (full_df.LEVEL == level) &
                         (full_df.R_BITS == r_bits)]

            bgf_n_errors_df = bgf_df[(bgf_df.R_BITS == r_bits) & (bgf_df.LEVEL == level)]

            try:
                bgf_errors_left = bgf_n_errors_df.iloc[0].av_errors_left
                tgt_n_errors_df = min(T1, bgf_errors_left)


                # candidates = df[df.max_errors_left < tgt_n_errors_df]
                candidates = df[df.av_errors_left == 0]
                # candidates = df[df.av_errors_left == 0]
                # print(candidates)


                best[level] = candidates.sort_values(['av_errors_left', 'max_errors_left', 'nflips']).iloc[0]
                print(f'{level=}, {best[level].R_BITS=}, {bgf_errors_left=}, {best[level].nflips=}, {best[level].av_errors_left=}')

                break
            except IndexError:
                continue


    return best

# plt.savefig('../figures/pickyfix_dfr.pdf')
def plot_dfr_all_levels(datafile='../../data/dfr/dfr_all.csv'):

    df_both = pd.read_csv(datafile)
    df_all = df_both[(df_both.decoder == 'PickyFix')]

    fig, axs = plt.subplots(3, 1, figsize=(LNCS_FIG_WIDTH, LNCS_BIG_FIG_HEIGHT))

    # for i_ax, level in enumerate([1, 3, 5]):
    for i_ax, level in enumerate([1, 3, 5]):
        ax = axs[i_ax]
        df = df_all[df_all.level == level]

        line_styles = ['-', 'dotted', 'dashed', 'dashdot']
        for j, it in enumerate(range(2, 6)):
            data = df[(df.decoder == 'PickyFix') & (df.n_iterations == it)]
            sns.lineplot(data=data, x='r_bits', y='dfr', ax=ax,
                         label=f'{it}', lw=0.5, color='0', ls=line_styles[j],
                         marker='.', ms=3, markeredgecolor='0')

        ax.set_title(f'Level {level}', y=1)

        ax.legend(title='Iterations', loc='upper right', fontsize=9)

        ax.set_yscale('log', base=2)

        # if i_ax == 2:
            # ax.set_xlabel(r'Parameter $r$')
        # else:
            # ax.set_xlabel(r'')


        ax.set_xlabel(r'Parameter $r$')

        ax.set_ylabel(r'DFR')

        sns.despine()

    axs[0].set_xlim(9500, 10700)
    axs[0].set_ylim(2**-20, 2)
    axs[0].set_yticks([2**-i for i in range(0, 23, 4)])

    axs[1].set_xlim(19200, 20600)
    axs[1].set_ylim(2**-20, 2)
    axs[1].set_yticks([2**-i for i in range(0, 23, 4)])

    axs[2].set_xlim(33400, 34600)
    axs[2].set_ylim(2**-20, 2)
    axs[2].set_yticks([2**-i for i in range(0, 23, 4)])

    plt.tight_layout()

    return axs


# plt.savefig('../figures/concavity_bgf_level1.pdf')
def plot_concavity_bgf_level1(datafile='../../data/concavity/bgf_level1.csv'):

    df = pd.read_csv(datafile)

    fig, ax = plt.subplots(1, figsize=(LNCS_FIG_WIDTH, LNCS_SMALL_FIG_HEIGHT))

    # markers = ['|', 'v', 's', 'p']
    markers = ['.', '.', '.', '.']
    line_styles = ['-', 'dotted', 'dashed', 'dashdot']
    for i, error_weight in enumerate([155, 153, 151]):
        ax = sns.lineplot(data=df[df.error_weight == error_weight], x='r_bits', y='dfr', marker=markers[i],
                          ls=line_styles[i],
                          lw=0.6, ms=2.5, markeredgecolor='black', color='black', label=f'{error_weight}', ax=ax)


    ax.set_yscale('log', base=2)


    ax.set_xlabel(r'Parameter $r$')
    ax.set_ylabel(r'DFR')

    ax.set_xlim((10000, 12500))
    ax.set_ylim((2**(-14), 2))
    ax.legend(title='Parameter $t$')
    ax.xaxis.set_tick_params(width=0.5)
    ax.yaxis.set_tick_params(width=0.5)

    sns.despine()
    plt.tight_layout()

    return ax


# plt.savefig('../figures/concavity_pf_level1.pdf')
def plot_concavity_pf_level1(datafile='../../data/concavity/pf_level1.csv'):

    df = pd.read_csv(datafile)

    fig, ax = plt.subplots(1, figsize=(LNCS_FIG_WIDTH, LNCS_SMALL_FIG_HEIGHT))

    # markers = ['|', 'v', 's', 'p']
    markers = ['.', '.', '.', '.']
    line_styles = ['-', 'dotted', 'dashed', 'dashdot']
    for i, n_iterations in enumerate([2, 3, 4, 5]):
        ax = sns.lineplot(data=df[df.n_iterations == n_iterations], x='r_bits', y='dfr', marker=markers[i],
                          ls=line_styles[i],
                          lw=0.6, ms=2.5, markeredgecolor='black', color='black', label=f'{n_iterations}', ax=ax)


    ax.set_yscale('log', base=2)


    ax.set_xlabel(r'Parameter $r$')
    ax.set_ylabel(r'DFR')

    ax.set_xlim((10000, 12500))
    ax.set_ylim((2**(-18), 2))
    ax.legend(title='Iterations')
    ax.xaxis.set_tick_params(width=0.5)
    ax.yaxis.set_tick_params(width=0.5)

    sns.despine()
    plt.tight_layout()

    return ax


def show_speedup_table(datafile='../../data/performance/all.csv'):
    df = pd.read_csv(datafile, comment='#')

    def get_bgf_reference(row):
        return df[(df.decoder == 'BGF') &
                  (df.level == row.level) &
                  (df.implementation == row.implementation)].iloc[0]


    pf_df = df[df.decoder == 'PickyFix'].sort_values(['implementation', 'level', 'n_iterations'])
    for i, row in pf_df.iterrows():
        speedup = round(get_bgf_reference(row).cycles/row.cycles, 2)
        print(row.implementation, row.level, row.n_iterations, row.r_bits, round(row.cycles), speedup)




def generate_all_plots(output_dir='../figures'):

    plot_dfr_bgf_level1(datafile='../../data/dfr/bgf_level1.csv')
    plt.savefig(os.path.join(output_dir, 'dfr_bgf_level1.pdf'))
    plt.close()

    plot_dfr_extrapolation_method()
    plt.savefig(os.path.join(output_dir, 'dfr_extrapolation_level1.pdf'))
    plt.close()

    plot_counters(datafile='../../data/counters/counters_level5.csv')
    plt.savefig(os.path.join(output_dir, 'counters_level5.pdf'))
    plt.close()

    plot_compare_n_errors(datafile='../../data/compare_n_errors/n_errors.csv')
    plt.savefig(os.path.join(output_dir, 'compare_n_errors.pdf'))
    plt.close()

    plot_threshold_problem(datafile='../../data/threshold/level1.csv')
    plt.savefig(os.path.join(output_dir, 'bgf_threshold_problem.pdf'))
    plt.close()

    plot_dfr_all_levels(datafile='../../data/dfr/dfr_all.csv')
    plt.savefig(os.path.join(output_dir, 'pickyfix_dfr.pdf'))
    plt.close()

    plot_concavity_bgf_level1(datafile='../../data/concavity/bgf_level1.csv')
    plt.savefig(os.path.join(output_dir, 'concavity_bgf_level1.pdf'))
    plt.close()

    plot_concavity_pf_level1(datafile='../../data/concavity/pf_level1.csv')
    plt.savefig(os.path.join(output_dir, 'concavity_pf_level1.pdf'))
    plt.close()

