#!/usr/bin/env python3

import re
import sys
import pandas as pd
import matplotlib as mpl
import matplotlib.pyplot as plt
import numpy as np
from matplotlib2tikz import save as tikz_save
from matplotlib.ticker import FuncFormatter
import matplotlib.ticker as mtick

def normalize(n):
    x = n.replace("$openang$", "<").replace("$closeang$", ">") \
        .replace("$opensqu$", "[").replace("$closesqu$", "]") \
        .replace("$opencur$", "{").replace("$closecur$", "}") \
        .replace("$$", "::")[2:]
    if "$_beg_" in x:
        return re.search(r'(.*)\$_beg_.+', x).group(1)
    else:
        return x

data = pd.read_csv("reports/union.csv", names=["event", "function", "duration"])
data["name"] = data["function"].apply(normalize)

clean_data = data.groupby("name").tail(3)
assert len(clean_data) % 3 == 0

supported = pd.read_csv("supported/union.csv", names=["name"])
supported_function_names = frozenset(supported["name"])
print("There are {} supported functions".format(len(supported_function_names)))

clean_filtered_data = clean_data[clean_data.name.isin(supported_function_names)]
assert len(clean_filtered_data) % 3 == 0
print("There are {} verified supported functions".format(len(clean_filtered_data)/3))

#print(clean_filtered_data)

mean_data = clean_filtered_data.groupby("name").mean()

#width = 2.42
#height = 1.5
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
#plt.xlabel('Verification time (s)')
#plt.ylabel('Number of functions')
#plt.annotate('100\%', xy=(50, 115), rotation=55, color='k', alpha=0.8, fontfamily='serif', fontsize='small')
#plt.annotate("50\%", xy=(155, 118), rotation=36.7, color='k', alpha=0.8, fontfamily='serif', fontsize='small')
#plt.annotate("10\%", xy=(215, 33), rotation=8, color='k', alpha=0.8, fontfamily='serif', fontsize='small')

ax.set_axisbelow(True)

plt.grid(color='lightgray', linestyle='--', linewidth=1)

sorted_data = np.sort(mean_data["duration"] / 1000)
plt.step(
    np.concatenate([sorted_data, sorted_data[[-1]]]),
    np.arange(sorted_data.size+1) / sorted_data.size,
    c="#003693",
    #marker='o',
    #linewidth=0,
    #markersize=1,
)

ax.yaxis.set_major_formatter(mtick.PercentFormatter(1.0))

# plt.plot(
#     base[:-1],
#     cumulative,
#     marker='o',
#     linewidth=1,
#     markersize=0,
#     #log=True,
#     c="#003693",
#     #cumulative=True,
#     #histtype="step"
# )

#for spine in ['top', 'right']:
#    ax.spines[spine].set_visible(False)
#for spine in ['left', 'bottom']:
#    ax.spines[spine].set_color('lightgray')
#    ax.spines[spine].set_linewidth(0.5)
#ax.xaxis.set_ticks_position('bottom')
#ax.yaxis.set_ticks_position('left')
#for axis in [ax.xaxis, ax.yaxis]:
#    axis.set_tick_params(direction='out', color='lightgray')

plt.xlim(left=0, right=5)
plt.ylim(bottom=0, top=1)
#plt.rc('text', usetex=True)
plt.tight_layout()

#ax.set_axis_off()
plt.subplots_adjust(top=1, bottom=0, right=1, left=0, hspace=0, wspace=0)
plt.margins(0, 0)
#ax.xaxis.set_major_locator(NullLocator())
#ax.yaxis.set_major_locator(NullLocator())
plt.savefig("plot3.pdf", bbox_inches='tight', pad_inches=0)
plt.savefig("plot3.pgf", bbox_inches='tight', pad_inches=0)
#plt.show()

tikz_save("plot3.tex")


print("Functions that are slow to verify")
print(len(mean_data[mean_data.duration > 10*1000]))

print("Maximum verification duration")
print(mean_data.duration.max())
