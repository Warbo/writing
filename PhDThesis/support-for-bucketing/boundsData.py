#!/usr/bin/env python3
# -*- coding: utf-8 -*-
import json
import sys
#reload(sys)
#sys.setdefaultencoding('utf8')

msg = lambda x: (sys.stderr.write(repr(x)), sys.stderr.flush(), None)[-1]

# Input format:
#   {
#     size: {
#       rep: {
#         "proportions": {
#           bucketCount: {
#             "min"/"max": {
#               "proportion": number
#   ...
data = json.load(sys.stdin)

# Average over the reps
average  = lambda l: sum(l) / len(l)
averaged = {
    size: {
        bucketCount: {
            bound: average([
                rep["proportions"][bucketCount][bound]["proportion"] \
                for rep in reps.values()
            ]) for bound in ["min", "max"]
        } for bucketCount in reps["1"]["proportions"].keys()  # "1" is arbitrary
    } for (size,reps) in data.items()
}

# Lines for our chart
def getLines(bound):
    return {
        bucketCount: [
            averaged[size][bucketCount][bound]           \
            for size in sorted(averaged.keys(), key=int) \
            if bucketCount in averaged[size]
        ] for bucketCount in averaged["10"].keys()
    }
minima = getLines("min")
maxima = getLines("max")
del getLines

# Show hash line for context
import os
hashprops = None
with open(os.getenv('proportionsTsv'), 'r') as f:
    # method, size, bucketCount, mean, stddev
    rows = [line.strip().split('	') for line in f.readlines() \
                                           if line.startswith('hashed')]

    sizes        = sorted(list(set([row[1] for row in rows])), key=int)
    bucketCounts = sorted(list(set([row[2] for row in rows])), key=int)

    hashprops = {
        bucketCount: [
            float([row[3] for row in rows if row[1] == size and         \
                                             row[2] == bucketCount][0]) \
            for size in sizes
        ] for bucketCount in bucketCounts
    }

# Based on https://python-graph-gallery.com/125-small-multiples-for-line-chart
import warnings
warnings.filterwarnings('ignore', module='matplotlib')

# Must be done before importing matplotlob.pyplot
# Taken from http://bkanuka.com/articles/native-latex-plots
import numpy      as np
import matplotlib as mpl
from math import sqrt
def figSize(widthFraction, height=None):
    textWidthPt = float(os.getenv('textWidth'))
    ptToInch    = 1.0 / 72.27
    textWidthIn = textWidthPt * ptToInch
    goldMean    = (sqrt(5.0)-1.0) / 2.0
    calcWidth   = widthFraction * textWidthIn
    calcHeight  = textWidthIn * ((goldMean * widthFraction) \
                                 if height is None else height)
    return (10, 10) # TODO: (calcWidth, calcHeight)

mpl.rcParams.update({
    # 'pgf.texsystem' : 'pdflatex',
    # 'text.latex.unicode': True,
    # 'text.usetex'   : True,  # Use LaTeX to write all text

    # # '[]' causes fonts to be inherited from document
    # 'font.family'     : 'serif',
    # 'font.serif'      : [],
    # 'font.sans-serif' : [],
    # 'font.monospace'  : [],

    # # LaTeX default is 10pt font.
    # 'axes.labelsize'  : 10,
    # 'font.size'       : 10,
    # 'legend.fontsize' : 8,
    # 'xtick.labelsize' : 8,
    # 'ytick.labelsize' : 8,

    'figure.figsize'  : figSize(0.9),  # Set a default

    # plots will be generated using this preamble. Use UTF-8.
    # 'pgf.preamble': [
    #     #r'\usepackage[utf8x]{inputenc}',
    #     #r'\usepackage[T1]{fontenc}',
    # ]
})

import matplotlib.pyplot as plt

# Inspired by https://stackoverflow.com/a/29107972/884682
def suplabels(x=None, y=None):
    ''' Add super ylabel or xlabel to the figure
    Similar to matplotlib.suptitle
    axis       - string: "x" or "y"
    label      - string
    '''
    fig  = plt.gcf()
    pos  = lambda a: min([ax.get_position().__getattribute__(a) \
                            for ax in fig.axes])

    draw = lambda p: plt.text(p['x'], p['y'], p['label'],
                              rotation  = p['rotation'],
                              transform = fig.transFigure,
                              ha        = 'center',
                              va        = 'center')
    draw({'rotation' : 0,
          'x'        : 0.5,
          'y'        : pos('ymin') - 5.0 / fig.dpi,
          'label'    : x})
    draw({'rotation' : 90,
          'x'        : pos('xmin') - 5.0 / fig.dpi,
          'y'        : 0.5,
          'label'    : y})

# Create a full width/height dummy plot to hold labels
#fig = plt.figure()
#ax  = fig.add_subplot(111)
#ax1 = fig.add_subplot(211)
#ax2 = fig.add_subplot(212)
# [ax.spines[edge].set_color('none') \
#  for edge in ['top', 'bottom', 'left', 'right']]

# ax.tick_params(labelcolor = 'w',
#                top        = 'off',
#                bottom     = 'off',
#                left       = 'off',
#                right      = 'off')

# ax.set_xlabel('Sample size')
# ax.set_ylabel('Available proportion')
# ax.set_title("Optimal, Pessimal and Random Signature Selection")

palette = plt.get_cmap(name='Set1')

plotIndex = 0
for bucketCount in range(2, 11):
    color = palette(0.1) #plotIndex / 10)
    plotIndex += 1

    # Find the right spot on the plot
    plt.subplot(3, 3, plotIndex)

    # Plot the lineplot
    xs = list(range(bucketCount, 11))

    plt.fill_between(xs,
                     minima[str(bucketCount)],
                     maxima[str(bucketCount)],
                     color = color,
                     alpha = 0.75)

    plt.plot(range(1, 11),
             hashprops[str(bucketCount)][0:10],
             marker    = '',
             color     = 'black',
             linewidth = 1.0,
             alpha     = 0.25)
    plt.plot(xs,
             minima[str(bucketCount)],
             marker   = '',
             color    = color,
             linewidth= 1.0,
             alpha    = 1.0,
             label    = str(bucketCount))
    plt.plot(xs,
             maxima[str(bucketCount)],
             marker   = '',
             color    = color,
             linewidth= 1.0,
             alpha    = 1.0,
             label    = str(bucketCount))

    # Same limits for everybody!
    plt.xlim(0, 10)
    plt.ylim(0, 1 )

    # Not ticks everywhere
    if plotIndex in range(7) :
        plt.tick_params(labelbottom='off')
    if plotIndex not in [1, 4, 7] :
        plt.tick_params(labelleft='off')

    # Add title
    plt.title(str(bucketCount),
              loc        = 'left',
              fontsize   = 12,
              fontweight = 0,
              color      = color)

plt.suptitle("Optimal, Pessimal and Random Signature Selection Quality",
             fontweight=2.)

suplabels(x='Sample size', y='Available proportion')

plt.savefig('bounds.png', dpi=300)
#plt.savefig('bounds.pgf')
#plt.savefig('bounds.pdf')
