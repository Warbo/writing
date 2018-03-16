#!/usr/bin/env python
from json import loads, dumps
import os
import sys
msg = lambda x: sys.stderr.write(x + '\n')

msg('Reading input')

from json import load

def readInput(sys):
    var = os.getenv(sys + 'Data')

    assert var is not None, 'No {} env var given'.format(sys)

    with open(var, 'r') as f:
        return load(f)

data = {
    'isacosy'   : readInput('isacosy'),
    'quickspec' : readInput('quickspec')
}
del(readInput)

msg('Normalising data')

# Extract timeout from one of the QuickSpec runs, since IsaCoSy may not have
# stored it
timeout = data['quickspec'].values()[0].values()[0]['timeout']

def normalise(data):
    def makeHashable(x):
        """Convert lists and dictionaries into tuples, recursively, so we can
        turn them into sets for comparison."""
        xType    = type(x)
        reducers = {
            type([]) : lambda rest, elem: rest +  (makeHashable(elem),),
            type({}) : lambda rest, key:  rest + ((makeHashable(key),
                                                   makeHashable(x[key])),)
        }
        return reduce(reducers[xType], x, ()) if xType in reducers else x

    for size in data:
        for rep in data[size]:
            # Samples should be sets
            data[size][rep]['sample'] = frozenset(data[size][rep]['sample'])

            # So should found equations
            data[size][rep]['found'] = frozenset(
                makeHashable(data[size][rep]['found']))
    return data

data = {
    'isacosy'   : normalise(data['isacosy'  ]),
    'quickspec' : normalise(data['quickspec'])
}

del(normalise)

def quickspecCheck(data):
    foundResults = {}

    for size in data:
        for rep in data[size]:
            rdata = data[size][rep]
            found = rdata['found']

            if len(found) > 0:
                for known in foundResults:
                    if len(foundResults[known]) > 0:
                        if rdata['sample'].issubset(known):
                            assert found.issubset(foundResults[known]), repr({
                                'error'  : 'More names should give more output',
                                'got'    : list(found),
                                'known'  : list(known),
                                'prev'   : list(foundResults[known]),
                                'sample' : list(sample),
                                'size'   : size
                            })
                        if rdata['sample'].issuperset(known):
                            assert found.issuperset(foundResults[known]), repr({
                                'error'  : 'More names should give more output',
                                'got'    : list(got),
                                'known'  : list(known),
                                'prev'   : list(foundResults[known]),
                                'sample' : list(sample),
                                'size'   : size
                            })

def sanityCheck(data):
    groundTruthNames = lambda raw: sorted(map(lambda x: x['file'], raw))

    for system in data.keys():
        for size in data[system]:
            for rep in data[system][size]:
                rdata       = data[system][size][rep]
                sample      = rdata['sample']
                groundTruth = groundTruthNames(rdata['wanted'])

                assert len(groundTruth) >= 1, debugInfo('Empty ground truth')

                if 'timeout' in rdata:
                    assert timeout == rdata['timeout'], \
                        'Got different timeouts {} and {}'.format(
                            str(timeout),
                            str(rdata['timeout']))

                if not rdata['success']:
                    assert rdata['found'] == frozenset([]), repr({
                        'error'  : 'Found conjectures for failing run',
                        'system' : system,
                        'size'   : size,
                        'rep'    : rep
                    })

                # Make sure every system is using the same samples/ground truth
                for sys in data.keys():
                    sysSample = data[sys][size][rep]['sample']
                    assert sysSample == sample, \
                        'Samples differ {0} {1} {2} {3}'.format(
                            system, sys, sample, sysSample)

                    sysGroundTruth = groundTruthNames(
                        data[sys][size][rep]['wanted'])
                    assert sysGroundTruth == groundTruth, \
                        'Ground truths differ {0} {1} {2} {3}'.format(
                            system, sys, groundTruth, sysGroundTruth)

                # Make sure any other occurrences of this sample got the same
                # ground truth and exploration output
                for otherRep in data[system][size].keys():
                    otherSample = data[system][size][otherRep]['sample']
                    if otherSample == sample:
                        otherGT = groundTruthNames(
                            data[system][size][otherRep]['wanted'])

                        assert groundTruth == otherGT, repr({
                            'error'       : 'Ground truths differ',
                            'rep'         : rep,
                            'otherRep'    : otherRep,
                            'sample'      : sample,
                            'otherSample' : otherSample
                        })

                        found, oFound = [sorted(x['found']) for x in \
                                         [rdata, data[system][size][otherRep]]]

                        if len(found) > 0 and len(oFound) > 0:
                            assert found == oFound, repr({
                                'error'       : 'Outputs differ on same sample',
                                'found'       : found,
                                'other'       : oFound,
                                'rep'         : rep,
                                'otherRep'    : otherRep,
                                'sample'      : list(sample),
                                'othersample' : list(otherSample),
                                'size'        : size,
                                'system'      : system
                            })

sanityCheck(data)
quickspecCheck(data['quickspec'])

del(sanityCheck)
del(quickspecCheck)

msg('Aggregating data')

def aggregateData(data):
    '''Pull numbers out of the given JSON results, to build up the data series
    needed for our graphs.'''
    import subprocess
    num = lambda x: type(x) in [type(42), type(42.0)]

    agg = {
        'correct'   : [],
        'found'     : [],
        'precHue'   : [],
        'precision' : [],
        'recall'    : [],
        'recHue'    : [],
        'size'      : [],
        'success'   : [],
        'time'      : [],
        'timeHue'   : [],
        'wanted'    : []
    }

    for size in sorted(map(int, data.keys())):
        msg('Extracting data for size ' + str(size))
        sdata = data[str(size)]
        for rep in sorted(map(int, sdata.keys())):
            rdata  = sdata[str(rep)]
            sample = rdata['sample']
            got    = rdata['found']

            found   = len(got)
            correct = len([x for x in rdata['wanted'] if x['found']])
            wanted  = len(rdata['wanted'])

            # We use min since killing might take some time
            t = min(rdata['time'], timeout)
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
            agg['correct'  ].append(correct)
            agg['found'    ].append(found)
            agg['precision'].append(p)
            agg['precHue'  ].append(wanted)
            agg['recall'   ].append(r)
            agg['recHue'   ].append(wanted)
            agg['size'     ].append(size)
            agg['success'  ].append(rdata['success'])
            agg['time'     ].append(t)
            agg['timeHue'  ].append(found + 1 if rdata['success'] else 0)
            agg['wanted'   ].append(wanted)

    return agg

aggs = {
    'isacosy'   : aggregateData(data['isacosy'  ]),
    'quickspec' : aggregateData(data['quickspec'])
}

del(aggregateData)
del(data)

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

def makeColours(agg):
    def go(key):
        from matplotlib.colors import ListedColormap
        maxVal    = max([agg[key][i] for i,s in enumerate(agg['success']) if s])
        colourMap = sns.color_palette('viridis', maxVal + 1).as_hex()
        msg('Highest {0} count is {1}'.format(key, maxVal))
        with open('highest_{0}_count'.format(key), 'w') as f:
            f.write(str(maxVal))
        return {
            'cmap'    : ListedColormap(colourMap),
            'norm'    : mpl.colors.Normalize(vmin=0, vmax=maxVal),
            'palette' : dict(enumerate(['#ff0000'] + colourMap \
                                       if key == 'found' else colourMap))
        }
    return go

for system in aggs:
    aggs[system]['found colours'], aggs[system]['wanted colours'] = \
        map(makeColours(aggs[system]), ['found', 'wanted'])

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

def drawPoints(agg, y=None, colours=None, hue=None, yLabel=None, ax=None,
               condition=None):
    '''Draw a scatter plot of agg[y][n] against agg['size'][n], for each point
    n. Points will be spread out horizontally to avoid overlaps, and the colour
    of each will be colours['palette'][agg[hue][n]].

    If condition is given, we filter the data to only keep those where filter(n)
    returns True, where n is the index as above.

    The the x-axis will be labelled with "Sample size", the y-axis with yLabel.

    The resulting plot (axes) are returned. To draw on existing axes, pass them
    in as ax.'''

    # Filter data, if asked
    if condition is not None:
        keepIndices = filter(condition, [i for i, s in enumerate(agg['size'])])
        keepers     = lambda key: [agg[key][i] for i in keepIndices]
        agg = {
            'size' : keepers('size'),
            y      : keepers(y),
            hue    : keepers(hue)
        }

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

def drawColourBar(ax=None, cax=None, colours=None, kw={}, label=None):
    '''Add a colour bar below ax or on cax.'''
    if cax is None:
        cax, kw2 = mpl.colorbar.make_axes_gridspec(
                       ax,
                       orientation = 'horizontal',  # Keeps plot full width
                       pad         = 0.18)          # 0.15 would cover x-label
        kw = dict(kw.items() + kw2.items())

    cbar = mpl.colorbar.ColorbarBase(
               cax,
               cmap = colours['cmap'],
               norm = colours['norm'],
               **kw)

    cbar.set_label(label)

    # Prevent problems with PDF output
    # See http://matplotlib.org/api/pyplot_api.html#matplotlib.pyplot.colorbar
    cbar.solids.set_edgecolor('face')

def savePlot(name):
    '''Write our the current figure as LaTeX.'''
    plt.tight_layout()
    plt.savefig(name + '.pgf', bbox_inches='tight', pad_inches=0.0)

def plotTime(system, agg):
    newFigure('time')

    plt.ylim(0, 300)

    sns.boxplot(data      = agg,
                x         = 'size',
                y         = 'time',
                color     = '0.95',
                fliersize = 0)

    ax = drawPoints(
        agg,
        colours = agg['found colours'],
        hue     = 'timeHue',
        y       = 'time',
        yLabel  = 'Runtime (seconds)')

    drawColourBar(ax      = ax,
                  colours = agg['found colours'],
                  label   = 'Conjectures found')
    savePlot(system + 'time')

def aggProp(system, sizes=None, agg=None, key=None, total=None):
    '''We assume the output conjectures from each run are bernoulli trials, i.e.
    whether it's good or bad is modelled as a (biased) coin toss, where the bias
    depends on the "quality" of the algorithm.'''

    import math

    sizeIndices   = lambda s: [i for i, x in enumerate(agg['size']) if x == s]
    entriesOfSize = lambda s, k: [agg[k][i] for i in sizeIndices(s)]
    runsOfSize    = lambda s: entriesOfSize(s, key)

    # There are many analyses we could perform. We implement a few, so we can
    # check that the results behave as we expect.

    noneToZero = lambda x: 0.0 if x is None else float(x)

    def ratioOfAverages(size):
        '''Assume that the measure of interest (precision or recall) is fixed
        for this size, and each particular conjecture is a bernoulli trial with
        this measure as its p parameter.
        Under this assumption, the fact that conjectures come from different
        runs is irrelevant, so we pool them all together into one binomial
        experiment.'''

        # Skip runs which timed out, since we'd rather keep the measurements of
        # running time separate to "quality"
        indices = [i for i in sizeIndices(size) if agg['success'][i]]

        # Precision may have found 0 conjectures, so we skip those points too
        # (as we can't define a wanted/unwanted proportion for an empty set).
        # Recall should never have 0 ground truths, since our sampling should
        # prevent it.
        if key == 'precision':
            indices = [i for i in indices if agg[total][i] != 0]

        totals   = [agg[total    ][i] for i in indices]
        corrects = [agg['correct'][i] for i in indices]

        debug = lambda err: repr({
            'error'    : err,
            'key'      : key,
            'totals'   : totals,
            'corrects' : corrects,
            'indices'  : indices,
            'system'   : system
        })
        assert 0    not in totals, debug('Got 0 total, even for success')
        assert None not in totals, debug('Got None total, even for success')

        # Bail out if we have no results for this size
        if len(totals) == 0:
            return {
                'bailed out' : True,
                'size'       : size
            }

        count   = float(sum(totals))
        correct = float(sum(corrects))

        p       = correct / count

        # Analytic values, calculated from our model
        anVar     = (p * (1.0 - p)) / count
        anStddev  = math.sqrt(anVar)
        anStderr  = anStddev / math.sqrt(count)

        # Sample variability, calculated from our data.
        if len(totals) == 1:
            # If we only have one data point, our sample standard deviation is
            # undefined (that point will be our mean, so the squared deviation
            # will be zero, and n - 1 will be zero, so we get 0 / 0). In this
            # case, we just use a value of 1, since that's the worst case.
            msg(repr({
                'warning': 'Only sampled 1 datapoint for this size',
                'size'   : size,
                'key'    : key,
                'system' : system
            }))
            sVar    = 1.0
            sStddev = 1.0
        else:
            # Variance is the average squared difference between each run's
            # actual correct proportion and the correct proportion we got from
            # the model (p).
            denom   = float(len(totals)) - 1.0
            sVar    = (sum([((float(correct) / tot) - p)**2 \
                            for tot, correct in zip(totals, corrects)])) / denom
            sStddev = math.sqrt(sVar)

        return {
            'bailed out'        : False,
            'size'              : size,
            'mean'              : p,
            'analytic variance' : anVar,
            'analytic stddev'   : anStddev,
            'analytic stderr'   : anStderr,
            'sample variance'   : sVar,
            'sample stddev'     : sStddev
        }

    # Calculate values for graph

    means   = []
    stdDevs = []
    for result in map(ratioOfAverages, sizes):
        if result['bailed out']:
            # Report the missing data so we can mention it in the paper
            msg(repr({
                'warning' : 'Size had no valid statistics',
                'size'    : result['size'],
                'key'     : key,
                'system'  : system
            }))

            # Pad the entries, to maintain alignment with x-axis labels
            means   += [None]
            stdDevs += [None]
        else:
            means   += [result['mean']]
            stdDevs += [result['sample stddev']]

    # Mean values +/- standard error
    low  = [None if mean is None else max(0, mean - stdDev) \
            for mean, stdDev in zip(means, stdDevs)]
    high = [None if mean is None else min(1, mean + stdDev) \
            for mean, stdDev in zip(means, stdDevs)]

    return means, low, high

def plotPrecRec(system, agg):
    sizes = sorted(list(set(agg['size'])))

    # matplotlib seems to count up 0, 1, 2, ... regardless of the x label, so we
    # need to shift and scale the points
    xs = map(lambda x: (x - min(sizes)) / (sizes[1] - sizes[0]), sizes)

    precData = aggProp(system, sizes, agg, 'precision', 'found' )
    recData  = aggProp(system, sizes, agg, 'recall',    'wanted')

    # Since there might be sizes missing (when e.g. all runs die), we need to
    # skip those data points
    stripNones = lambda l: filter(lambda elem: elem is not None, l)

    precXs = [x for x, m in zip(xs, precData[0]) if m is not None]
    recXs  = [x for x, m in zip(xs,  recData[0]) if m is not None]

    precMeans, precLows, precHighs = map(stripNones, precData)
    recMeans,  recLows,  recHighs  = map(stripNones,  recData)

    newFigure('precRec')
    gs            = mpl.gridspec.GridSpec(3, 1, height_ratios=[5, 5, 1])
    precAx, recAx = (plt.subplot(gs[0]), plt.subplot(gs[1]))

    map(lambda args: args['ax'].fill_between(args['xs'],
                                             args['lows'],
                                             args['highs'],
                                             #alpha     = 0.5,
                                             facecolor = '#CCCCCC',
                                             edgecolor = 'face'),
        [{'ax': precAx, 'xs': precXs, 'lows': precLows, 'highs': precHighs},
         {'ax':  recAx, 'xs':  recXs, 'lows':  recLows, 'highs':  recHighs}])

    succeeded = lambda i: agg['success'][i]

    drawPoints(
        agg,
        ax        = precAx,
        colours   = agg['wanted colours'],
        hue       = 'precHue',
        y         = 'precision',
        yLabel    = 'Precision',
        condition = succeeded)

    drawPoints(
        agg,
        ax        = recAx,
        colours   = agg['wanted colours'],
        hue       = 'recHue',
        y         = 'recall',
        yLabel    = 'Recall',
        condition = succeeded)

    [(ax.set_ylim(0, 1), ax.plot(xs, ms)) \
     for ax, xs, ms in [(precAx, precXs, precMeans),
                        ( recAx,  recXs,  recMeans)]]

    drawColourBar(
        cax     = plt.subplot(gs[2]),
        colours = agg['wanted colours'],
        kw      = {'orientation': 'horizontal'},
        label   = 'Ground truth theorems')

    savePlot(system + 'prec')

for system in aggs:
    plotTime(   system, aggs[system])
    plotPrecRec(system, aggs[system])
