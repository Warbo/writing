#!/usr/bin/env python3
from os import chdir, getenv, mkdir

# As proportion of textWidth
graphSize=(0.72, 0.72)

# Create the $out directory of our Nix derivation, to fill with graphs
out = getenv('out')
mkdir(out)
chdir(out)
del(chdir, mkdir)

textWidthPt = float(getenv('textWidth'))  # To scale graphs appropriately
processed   = getenv('processed') + '/out'
del(getenv)

# Read input JSON
from json import loads
data = None
with open(processed, 'r') as f:
    data = loads(f.read())
del(loads, processed)

# Extract all of the sizes and bucket counts
counts = []
sizes  = []
for size in data:
    sizes.append(int(size))
    for count in data[size]:
        counts.append(int(count))
counts = sorted(list(set(counts)))
sizes  = sorted(list(set(sizes )))

from math import sqrt
def meanStdDev(xs):
    num  = len(xs)
    mean = sum(xs) / len(xs)
    top  = sum([(x - mean)**2 for x in xs])
    frac = top / (num - 1)
    sdev = sqrt(frac)
    return (mean, sdev)

absMeans = {}
absErrs  = {}
for count in counts:
    absMeans[count] = {}
    absErrs[ count] = {}
    for size in sizes:
        hashed    = data[str(size)][str(count)]['hashed'   ]
        recurrent = data[str(size)][str(count)]['recurrent']
        absolutes = [(r - h) for h, r in zip(hashed, recurrent)]
        mean, stddev = meanStdDev(absolutes)
        absMeans[count][size] = mean
        absErrs[ count][size] = stddev

# Arrange data points into lists, which we can reference by key when plotting
points = {'size': sizes}
#points.update({
#    'count'+str(c): [data[str(s)][str(c)]['meandelta'] for s in sizes] \
#    for c in counts
#})
#points.update({
#    'err'+str(c): [data[str(s)][str(c)]['stddev'] for s in sizes] \
#    for c in counts
#})
points.update({
    'count'+str(c): [absMeans[c][s] for s in sizes] for c in counts
})
points.update({
    'err'+str(c): [absErrs[c][s] for s in sizes] for c in counts
})

# Plot each count

from math import sqrt
def figSize(widthFraction, height=None):
    ptToInch    = 1.0 / 72.27
    textWidthIn = textWidthPt * ptToInch
    goldMean    = (sqrt(5.0)-1.0) / 2.0
    calcWidth   = widthFraction * textWidthIn
    calcHeight  = textWidthIn * ((goldMean * widthFraction) \
                                 if height is None else height)
    return (10, 10) # TODO (calcWidth, calcHeight)

import matplotlib as mpl
mpl.rcParams.update({
    'figure.figsize'  : figSize(0.9),  # Set a default
})

import matplotlib.pyplot as plt

plotIndex = 0
for count in [5, 10, 15, 20]:
    #color = palette(0.1) #plotIndex / 10)
    plotIndex += 1

    # Find the right spot on the plot
    plt.subplot(2, 2, plotIndex)

    # Plot the lineplot

    plt.errorbar(data=points, x='size', y='count'+str(count),
                 yerr='err'+str(count),
                 ecolor='black', elinewidth=0.5, capsize=2)

    # Same limits for everybody!
    plt.xlim(0  , 100)
    plt.ylim(-10, 10 )

    # Not ticks everywhere
    if plotIndex in [1, 2]:
        plt.tick_params(labelbottom='off')
    if plotIndex not in [1, 3]:
        plt.tick_params(labelleft='off')

    # Add title
    plt.title(str(count),
              loc        = 'left',
              fontsize   = 12,
              fontweight = 0)

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

plt.suptitle("Extra Theorems Discoverable by Clustering",
             fontweight=2.)

suplabels(x='Sample size', y='Extra theorems (vs random)')

# Saving

#fig.set_size_inches(figSize(graphSize[0], graphSize[1]))
plt.savefig('foo.png', bbox_inches='tight', pad_inches=0.0)
plt.savefig('foo.pdf', bbox_inches='tight', pad_inches=0.0)
plt.savefig('foo.pgf', bbox_inches='tight', pad_inches=0.0)
