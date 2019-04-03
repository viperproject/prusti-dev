#!/usr/bin/env python3

import pandas as pd
import matplotlib as mpl
import matplotlib.pyplot as plt
import numpy as np
from math import sqrt
from matplotlib.ticker import NullLocator
from matplotlib2tikz import save as tikz_save

compilation_reports = [
    "compilation-report-2018-11-12-104249.csv",
    "compilation-report-2018-11-13-182045.csv",
    "compilation-report-2018-11-14-042009.csv"
]

prusti_reports = [
    "coarse-grained-verification-report-supported-procedures.csv-2019-04-02-221340-mod.csv",
    "coarse-grained-verification-report-supported-procedures.csv-2019-04-03-022504-mod.csv",
    "coarse-grained-verification-report-supported-procedures.csv-2019-04-03-063640-mod.csv"
]

verification_time_reports = [
    "verification-time-report-2019-04-02-221340.csv",
    "verification-time-report-2019-04-03-022504.csv",
    "verification-time-report-2019-04-03-063640.csv"
]

compilation_data = list(map(lambda x: pd.read_csv(x), compilation_reports))
prusti_data = list(map(lambda x: pd.read_csv(x), prusti_reports))
verification_time_data = list(map(lambda x: pd.read_csv(x), verification_time_reports))

successful_compilation_data = list(map(
    lambda df: df[df["Successful compilation"]][df["Duration (s)"] <= 900],
    compilation_data
))

for a, b in ((0, 1), (1, 2)):
    assert list(successful_compilation_data[a]["Crate name"]) == list(successful_compilation_data[b]["Crate name"])

successful_crates = set(successful_compilation_data[0]["Crate name"])

clean_prusti_data = list(map(
    lambda df: df[df["Crate name"].isin(successful_crates)],
    prusti_data
))

clean_verification_time_data = list(map(
    lambda df: df[df["Crate name"].isin(successful_crates)],
    verification_time_data
))

print("Slowest crates to verify:")
print(clean_verification_time_data[0][clean_verification_time_data[0]["Verification duration"] > 125])

for a in (0, 1, 2):
    assert list(clean_prusti_data[a]["Crate name"]) == list(successful_compilation_data[a]["Crate name"])

for a in (0, 1, 2):
    for index, row in clean_prusti_data[a].iterrows():
        name = row["Crate name"]
        assert row["Successful verification"], "Verification of {} failed".format(name)
        assert row["Whitelist items"] == row["Verified items"], "error in row {}".format(name)
        assert row["Verified items"] == row["Successful items"], "error in row {}".format(name)

for a in (0, 1, 2):
    #print(set(clean_verification_time_data[a]["Crate name"]) - set(successful_compilation_data[a]["Crate name"]))
    #print(set(successful_compilation_data[a]["Crate name"]) - set(clean_verification_time_data[a]["Crate name"]))
    assert list(clean_verification_time_data[a]["Crate name"]) == list(successful_compilation_data[a]["Crate name"])

crate_names = successful_compilation_data[0]["Crate name"]
crate_names.reset_index(drop=True, inplace=True)

average_compilation = sum([df["Duration (s)"] for df in successful_compilation_data]) / 3
average_compilation.reset_index(drop=True, inplace=True)

num_verified_functions = sum([df["Verified items"] for df in clean_prusti_data]) / 3
num_verified_functions.reset_index(drop=True, inplace=True)

num_dependencies = sum([df["Number of dependencies"] for df in clean_verification_time_data]) / 3
num_dependencies.reset_index(drop=True, inplace=True)

average_prusti_verification = sum([df["Duration (s)"] for df in clean_prusti_data]) / 3
average_prusti_verification.reset_index(drop=True, inplace=True)

average_verification_per_function = sum([df["Verification duration"] for df in clean_verification_time_data]) / 3
average_verification_per_function.reset_index(drop=True, inplace=True)
average_verification_per_function = average_verification_per_function / num_verified_functions

average_prusti_overhead = average_prusti_verification - average_compilation

print("Average verification time per function in a crate")
print(average_verification_per_function.head())

width = 3.5
height = 1.5
pgf_with_latex = {                      # setup matplotlib to use latex for output
    "pgf.texsystem": "pdflatex",        # change this if using xetex or lautex
    "text.usetex": True,                # use LaTeX to write all text
    "font.family": "serif",
    "font.serif": [],                   # blank entries should cause plots
    "font.sans-serif": [],              # to inherit fonts from the document
    "font.monospace": [],
    "axes.labelsize": 10,
    "font.size": 10,
    "legend.fontsize": 8,               # Make the legend/label fonts
    "xtick.labelsize": 8,               # a little smaller
    "ytick.labelsize": 8,
    "pgf.preamble": [
        r"\usepackage[utf8]{inputenc}", # use utf8 input and T1 fonts
        r"\usepackage[T1]{fontenc}",    # plots will be generated
        r"\usepackage{pgfplots}"        # using this preamble
    ]
}
#mpl.use("pgf")
mpl.rcParams.update(pgf_with_latex)

plt.rc('font', family='serif')
plt.rc('xtick', labelsize='x-small')
plt.rc('ytick', labelsize='x-small')

plt.figure(figsize=(width, height))
x = np.linspace(0, 400, 30)
ax = plt.subplot(1, 1, 1)
#plt.scatter(average_compilation, average_prusti_overhead, s=1, c="#0E47AE", marker="o", zorder=10)
#plt.scatter(average_compilation, average_viper_verification, c="#FF8649", s=1, marker="x", zorder=20)
#plt.scatter(average_compilation, average_viper_verification, c="#003284", s=1, marker="x", zorder=20)  # FF8649
#plt.scatter(average_compilation, average_prusti_overhead, c="#003693", s=1, marker=".", zorder=20)  # FF8649
#plt.legend(['Prusti overhead', 'Viper verification time'], loc='upper center', bbox_to_anchor=(0.5, 1))
#plt.plot(x, x, color='k', ls='--', linewidth=1, zorder=0, alpha=0.3)
#plt.plot(x, x/2, color='k', ls='--', linewidth=1, zorder=0, alpha=0.3)
#plt.plot(x, x/10, color='k', ls='--', linewidth=1, zorder=0, alpha=0.3)
plt.xlabel('Average verification time per function (s)')
plt.ylabel('Number of crates')
#plt.annotate('100\%', xy=(50, 115), rotation=55, color='k', alpha=0.8, fontfamily='serif', fontsize='small')
#plt.annotate("50\%", xy=(155, 118), rotation=36.7, color='k', alpha=0.8, fontfamily='serif', fontsize='small')
#plt.annotate("10\%", xy=(215, 33), rotation=8, color='k', alpha=0.8, fontfamily='serif', fontsize='small')

ax.set_axisbelow(True)
plt.grid(color='lightgray', linestyle='--', linewidth=1)

split=4
max_x=35
plt.hist(
    average_verification_per_function[average_verification_per_function > 0],
    #weights=num_verified_functions[average_verification_per_function > 0],
    bins=[x/split for x in range(max_x*(split)+1)],
    #log=True,
    color="#003693"
)

#for spine in ['top', 'right']:
#    ax.spines[spine].set_visible(False)
#for spine in ['left', 'bottom']:
#    ax.spines[spine].set_color('lightgray')
#    ax.spines[spine].set_linewidth(0.5)
#ax.xaxis.set_ticks_position('bottom')
#ax.yaxis.set_ticks_position('left')
#for axis in [ax.xaxis, ax.yaxis]:
#    axis.set_tick_params(direction='out', color='lightgray')

#plt.xlim(left=0, right=None)
#plt.ylim(bottom=0, top=None) #125)
#plt.rc('text', usetex=True)
plt.tight_layout()

#ax.set_axis_off()
plt.subplots_adjust(top=1, bottom=0, right=1, left=0, hspace=0, wspace=0)
plt.margins(0, 0)
#ax.xaxis.set_major_locator(NullLocator())
#ax.yaxis.set_major_locator(NullLocator())
plt.savefig("plot2.pdf", bbox_inches='tight', pad_inches=0)
plt.savefig("plot2.pgf", bbox_inches='tight', pad_inches=0)
#plt.show()

tikz_save("plot2.tex")
