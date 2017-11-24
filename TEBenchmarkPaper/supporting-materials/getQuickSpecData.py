#!/usr/bin/env python
from json import dumps
import os
import sys
msg = lambda x: sys.stderr.write(x + '\n')

msg('Reading input')

def readInput():
    from gzip import open
    from json import load
    with open(os.getenv('zipped'), 'r') as zipped:
        return load(zipped)['results']['quickspectip.track_data']['result'][0]

data = readInput()
del(readInput)

msg('Aggregating data')

def makeHashable(x):
        '''Convert lists and dictionaries into tuples, recursively, so we can
        turn them into sets for comparison.'''
        xType    = type(x)
        reducers = {
            type([]) : lambda rest, elem: rest +  (makeHashable(elem),),
            type({}) : lambda rest, key:  rest + ((makeHashable(key),
                                                   makeHashable(x[key])),)
        }
        return reduce(reducers[xType], x, ()) if xType in reducers else x

def sanityCheck(size, rep, rawSample, got, knownEqs):
    assert len(rawSample) == size, repr({
        'error'     : 'Wrong number of names sampled',
        'rep'       : rep,
        'rawSample' : rawSample,
        'size'      : size
    })

    sample = frozenset(rawSample)
    assert len(sample) == len(rawSample), repr({
        'error'     : 'Sampled names contain duplicates',
        'rep'       : rep,
        'rawSample' : rawSample,
        'sample'    : sample,
        'size'      : size
    })

    if sample in knownEqs:
        if knownEqs[sample] != got:
            msg(dumps({
                'error'  : 'Differing outputs for the same sample',
                'prev'   : list(knownEqs[sample]),
                'rep'    : rep,
                'sample' : list(got),
                'size'   : size
            }))

        if got is not None:
            for known in knownEqs:
                if knownEqs[known] is not None:
                    if sample.issubset(known):
                        if not got.issubset(knownEqs[known]):
                            msg(dumps({
                                'error'  : 'More names should give more output',
                                'got'    : list(got),
                                'known'  : list(known),
                                'prev'   : list(knownEqs[known]),
                                'sample' : list(sample),
                                'size'   : size
                            }))
                    if sample.issuperset(known):
                        if not got.issuperset(knownEqs[known]):
                            msg(dumps({
                                'error'  : 'More names should give more output',
                                'got'    : list(got),
                                'known'  : list(known),
                                'prev'   : list(knownEqs[known]),
                                'sample' : list(sample),
                                'size'   : size
                            }))

def aggregateData(data):
    num = lambda x: type(x) in [type(42), type(42.0)]

    agg = {
        'found'     : [],
        'precHue'   : [],
        'precision' : [],
        'recall'    : [],
        'recHue'    : [],
        'size'      : [],
        'time'      : [],
        'timeHue'   : [],
        'wanted'    : []
    }

    # Make a note of which equations are discoverable from each sample
    knownEqs = {}

    for size in sorted(map(int, data.keys())):
        msg('Extracting data for size ' + str(size))
        sdata = data[str(size)]['reps']
        for rep in sorted(map(int, sdata.keys())):
            rdata  = sdata[str(rep)]
            sample = frozenset(rdata['sample'])
            got    = frozenset(makeHashable(rdata['found'][0])) \
                     if rdata['success'] else None

            sanityCheck(size, rep, rdata['sample'], got, knownEqs)

            if sample in knownEqs:
                msg('Skipping dupe rep {0} of size {1}'.format(rep, size))
                continue

            knownEqs[sample] = got

            found  = len(got)             if rdata['success'] else 0
            wanted = len(rdata['wanted']) if rdata['success'] else 0

            # Get the time if available, otherwise treat as a timeout
            # We use min since killing might take some time
            t = min(rdata['time'], rdata['timeout'])
            assert num(t), 'Non-numeric time %r' % type(t)

            # Assume precision is 0 if not found
            p = rdata['precision'] if 'precision' in rdata else 0
            p = p or 0
            assert num(p), 'Non-numeric prec %r' % type(p)

            # Assume recall is 0 if not found
            r = rdata['recall'] if 'recall' in rdata else 0
            r = r or 0
            assert num(r), 'Non-numeric rec %r' % type(r)

            # Store in "wide format". We +1 the hues and use 0 for failure
            agg['found'    ].append(found)
            agg['precision'].append(p)
            agg['precHue'  ].append(wanted + 1 if rdata['success'] else 0)
            agg['recall'   ].append(r)
            agg['recHue'   ].append(wanted + 1 if rdata['success'] else 0)
            agg['size'     ].append(size)
            agg['time'     ].append(t)
            agg['timeHue'  ].append(found  + 1 if rdata['success'] else 0)
            agg['wanted'   ].append(wanted)

    return agg

agg = aggregateData(data)
del(data)
del(makeHashable)
del(sanityCheck)
del(aggregateData)

msg('Setting up plots')

import matplotlib as mpl
import numpy      as np

def figSize(widthFraction, height=None):
    with open(os.getenv('textWidth'), 'r') as textWidthFile:
        textWidthPt = float(textWidthFile.read())
    ptToInch    = 1.0 / 72.27
    textWidthIn = textWidthPt * ptToInch
    goldMean    = (np.sqrt(5.0)-1.0) / 2.0
    calcWidth   = widthFraction * textWidthIn
    calcHeight  = textWidthIn * ((goldMean * widthFraction) \
                                 if height is None else height)
    return (calcWidth, calcHeight)

# Must be done before importing matplotlob.pyplot
# Taken from http://bkanuka.com/articles/native-latex-plots
mpl.rcParams.update({
    'pgf.texsystem' : 'pdflatex',
    'text.usetex'   : True,  # Use LaTeX to write all text

    # '[]' causes fonts to be inherited from document
    'font.family'     : 'serif',
    'font.serif'      : [],
    'font.sans-serif' : [],
    'font.monospace'  : [],

    # LaTeX default is 10pt font.
    'axes.labelsize'  : 10,
    'text.fontsize'   : 10,
    'legend.fontsize' : 8,
    'xtick.labelsize' : 8,
    'ytick.labelsize' : 8,

    'figure.figsize'  : figSize(0.9),  # Set a default

    # plots will be generated using this preamble. Use UTF-8.
    'pgf.preamble': [
        r'\usepackage[utf8x]{inputenc}',
        r'\usepackage[T1]{fontenc}',
    ]
})

msg('Setting colour scales')

import matplotlib.pyplot as plt
import seaborn           as sns

def makeColours(key):
    from matplotlib.colors import ListedColormap
    maxVal    = max(agg[key])
    colourMap = sns.color_palette('viridis', maxVal + 1).as_hex()
    msg('Highest {0} count is {1}'.format(key, maxVal))
    return {
        'cmap'    : ListedColormap(colourMap),
        'norm'    : mpl.colors.Normalize(vmin=0, vmax=maxVal),
        'palette' : dict(enumerate(['#ff0000'] + colourMap))
    }

foundColours, wantedColours = map(makeColours, ['found', 'wanted'])

del(makeColours)

msg('Drawing plots')

def newFigure(name):
    '''Set up matplotlib/seaborn for a new figure. The name is used to look up
    dimensions from the environment. The figure's dimensions are returned.'''
    widthFrac     = float(os.getenv(name + 'WidthFraction'))
    heightFrac    = float(os.getenv(name + 'HeightFraction'))
    width, height = figSize(widthFrac, heightFrac)
    fig           = plt.figure(figsize=(width, height))

    sns.set_style('whitegrid')
    sns.set_context('paper')

    return fig

def drawPoints(y=None, colours=None, hue=None, yLabel=None, ax=None):
    '''Draw a scatter plot of agg[y][n] against agg['size'][n], for each point
    n. Points will be spread out horizontally to avoid overlaps, and the colour
    of each will be colours['palette'][agg[hue][n]].

    The the x-axis will be labelled with "Sample size", the y-axis with yLabel.

    The resulting plot (axes) are returned. To draw on existing axes, pass them
    in as ax.'''
    # Alternatively, we could use stripplot with jitter
    newAx = sns.swarmplot(data      = agg,
                          x         = 'size',
                          y         = y,
                          size      = 2,  # Marker size
                          edgecolor = 'k',
                          linewidth = 0.3,
                          palette   = colours['palette'],
                          hue       = hue,
                          ax        = ax)
    newAx.legend_.remove()
    newAx.set_xlabel('Sample size')
    newAx.set_ylabel(yLabel)
    return newAx

def drawColourBar(ax=None, cax=None, colours=None, label=None, fig=None):
    '''Add a colour bar below ax or on cax.'''
    if cax is None:
        cax, kw = mpl.colorbar.make_axes_gridspec(
                       ax,
                       orientation = 'horizontal',  # Keeps plot full width
                       pad         = 0.18)          # 0.15 would cover x-label
    else:
        kw = {}

    cbar = mpl.colorbar.ColorbarBase(
               cax,
               cmap = colours['cmap'],
               norm = colours['norm'],
               **kw)

    cbar.set_label(label)

    # Prevent problems with PDF output
    # See http://matplotlib.org/api/pyplot_api.html#matplotlib.pyplot.colorbar
    cbar.solids.set_edgecolor("face")

def savePlot(name):
    '''Write our the current figure as LaTeX.'''
    plt.tight_layout()
    plt.savefig(name + '.pgf', bbox_inches='tight', pad_inches=0.0)

def plotTime():
    newFigure('time')

    plt.ylim(0, 180)

    sns.boxplot(data      = agg,
                x         = 'size',
                y         = 'time',
                color     = '0.95',
                fliersize = 0)

    ax = drawPoints(
        colours = foundColours,
        hue     = 'timeHue',
        y       = 'time',
        yLabel  = 'Runtime (seconds)')

    drawColourBar(ax = ax, colours = foundColours, label = 'Conjectures found')
    savePlot('time')

def plotPrecRec():
    newFigure('precRec')
    gs     = mpl.gridspec.GridSpec(3, 1, height_ratios=[5, 5, 1])

    precAx = drawPoints(
        ax      = plt.subplot(gs[0]),
        colours = wantedColours,
        hue     = 'precHue',
        y       = 'precision',
        yLabel  = 'Precision')

    recAx = drawPoints(
        ax      = plt.subplot(gs[1]),
        colours = wantedColours,
        hue     = 'recHue',
        y       = 'recall',
        yLabel  = 'Recall')

    map(lambda ax: ax.set_ylim(0, 1), [precAx, recAx])

    cbar = mpl.colorbar.ColorbarBase(
               plt.subplot(gs[2]),
               cmap=wantedColours['cmap'],
               norm=wantedColours['norm'],
               orientation='horizontal')
    cbar.set_label('Ground truth theorems')

    # Prevent problems with PDF output
    # See http://matplotlib.org/api/pyplot_api.html#matplotlib.pyplot.colorbar
    cbar.solids.set_edgecolor("face")

    savePlot('prec')

plotTime()
plotPrecRec()
