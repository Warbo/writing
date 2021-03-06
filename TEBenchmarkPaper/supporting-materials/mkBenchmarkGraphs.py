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

            # Store in "wide format"
            agg['correct'  ].append(correct)
            agg['found'    ].append(found)
            agg['precision'].append(p)
            agg['precHue'  ].append(wanted)
            agg['recall'   ].append(r)
            agg['recHue'   ].append(wanted)
            agg['size'     ].append(size)
            agg['success'  ].append(rdata['success'])
            agg['time'     ].append(t)
            agg['timeHue'  ].append(found)
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
    #'text.usetex'   : True,  # Use LaTeX to write all text

    # '[]' causes fonts to be inherited from document
    'font.family'     : 'serif',
    #'font.serif'      : [],
    #'font.sans-serif' : [],
    #'font.monospace'  : [],

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

msg('Drawing plots')

import matplotlib.pyplot as plt
import seaborn           as sns

point = {'size': 1.5, 'linewidth': 0.35}
cross = {'size': 3  , 'linewidth': 0.8 }

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

def savePlot(name):
    '''Write our the current figure as LaTeX.'''
    plt.tight_layout()
    plt.savefig(name + '.eps', bbox_inches='tight', pad_inches=0.0)

def aggProp(system, sizes=None, agg=None, key=None, total=None):
    import math

    sizeIndices   = lambda s: [i for i, x in enumerate(agg['size']) if x == s]
    entriesOfSize = lambda s, k: [agg[k][i] for i in sizeIndices(s)]
    runsOfSize    = lambda s: entriesOfSize(s, key)

    noneToZero = lambda x: 0.0 if x is None else float(x)

    def averageOfRatios(size):
        '''Mean value across samples of the given size.'''

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

        ratios = [float(agg['correct'][i]) / float(agg[total][i]) \
                  for i in indices]

        debug = lambda err: repr({
            'error'    : err,
            'key'      : key,
            'totals'   : totals,
            'corrects' : corrects,
            'ratios'   : ratios,
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

        p = sum(ratios) / len(ratios)

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
            # actual ratio and the mean ratio
            sVar    = sum([(r - p)**2 for r in ratios]) / len(ratios)
            sStddev = math.sqrt(sVar)

        return {
            'bailed out'        : False,
            'size'              : size,
            'mean'              : p,
            'sample variance'   : sVar,
            'sample stddev'     : sStddev
        }

    # Calculate values for graph

    means   = []
    stdDevs = []
    for result in map(averageOfRatios, sizes):
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

def drawLineWithErrorBars(xs=None, ys=None, lows=None, highs=None, ax=None):
    assert ax is not None, 'drawLineWithErrorBars needs ax argument'
    assert len(set(map(len, [xs, ys, lows, highs]))) == 1, repr({
        'error': 'All data given to drawLineWithErrorBars need same length',
        'xs': xs, 'ys': ys, 'lows': lows, 'highs': highs
    })
    ax.errorbar(x=xs, y=ys, yerr=([h - y for h, y in zip(highs, ys)],
                                  [y - l for l, y in zip(lows,  ys)]),
                elinewidth=0.7,  # width of error bar line
                ecolor='k',      # color of error bar
                capsize=1.5,     # cap length for error bar
                capthick=0.7,    # cap thickness for error bar)
                zorder = 100)    # Draw above points

def plotPrecRec(system, agg):
    sizes = sorted(list(set(agg['size'])))

    # matplotlib seems to count up 0, 1, 2, ... regardless of the x label, so we
    # need to shift and scale the points
    xs = map(lambda x: (x - min(sizes)) / (sizes[1] - sizes[0]), sizes)

    pData = aggProp(system, sizes, agg, 'precision', 'found' )
    rData = aggProp(system, sizes, agg, 'recall',    'wanted')

    # Since there might be sizes missing (when e.g. all runs die), we need to
    # skip those data points
    stripNones = lambda l: filter(lambda elem: elem is not None, l)

    pXs = [x for x, m in zip(xs, pData[0]) if m is not None]
    rXs = [x for x, m in zip(xs, rData[0]) if m is not None]

    pMeans, pLows, pHighs = map(stripNones, pData)
    rMeans, rLows, rHighs = map(stripNones, rData)

    newFigure('precRec')
    gs       = mpl.gridspec.GridSpec(3, 1, height_ratios=[5, 5, 1])
    pAx, rAx = (plt.subplot(gs[0]), plt.subplot(gs[1]))
    [ax.set_ylim(0, 1) for ax in [pAx, rAx]]

    succeeded = lambda i: agg['success'][i]

    for args in [{'ax'     : pAx,
                  'hue'    : 'precHue',
                  'y'      : 'precision',
                  'yLabel' : 'Precision'},
                 {'ax'     : rAx,
                  'hue'    : 'recHue',
                  'y'      : 'recall',
                  'yLabel' : 'Recall'}]:
        keepIndices = filter(succeeded, [i for i, s in enumerate(agg['size'])])
        keepers     = lambda key: [agg[key][i] for i in keepIndices]
        newAgg = {
            'size'      : keepers('size'),
            args['y']   : keepers(args['y']),
        }

        # Alternatively, we could use stripplot with jitter
        newAx = sns.swarmplot(data      = newAgg,
                              x         = 'size',
                              y         = args['y'],
                              size      = point['size'],
                              edgecolor = 'k',
                              linewidth = point['linewidth'],
                              marker    = 'o',
                              color     = 'k',
                              ax        = args['ax'])
        if newAx.legend_: newAx.legend_.remove()
        newAx.set_xlabel('Sample size')
        newAx.set_ylabel(args['yLabel'])

    map(lambda args: drawLineWithErrorBars(xs     = args['xs'],
                                           ys     = args['ys'],
                                           lows   = args['lows'],
                                           highs  = args['highs'],
                                           ax     = args['ax']),
        [{'ax': pAx, 'xs': pXs, 'ys': pMeans, 'lows': pLows, 'highs': pHighs},
         {'ax': rAx, 'xs': rXs, 'ys': rMeans, 'lows': rLows, 'highs': rHighs}])

    savePlot(system + 'prec')

def plotQSTime():
    agg = aggs['quickspec']
    newFigure('time')

    plt.ylim(0, 300)
    sns.plt.xlim(1, 20)

    sns.boxplot(data      = agg,
                x         = 'size',
                y         = 'time',
                color     = '0.95',
                fliersize = 0)

    # Alternatively, we could use stripplot with jitter
    successes = [i for i,s in enumerate(agg['success']) if     s]
    failures  = [i for i,s in enumerate(agg['success']) if not s]
    listAtIndices = lambda idc, lst: [x for i,x in enumerate(lst) if i in idc]
    dictAtIndices = lambda idc: dict(agg,
                                     size=listAtIndices(idc, agg['size']),
                                     time=listAtIndices(idc, agg['time']))
    ax = plt.gca()
    ax.set_xlim(1, 20)  # Force X limits in case success and fail differ
    ax = sns.swarmplot(data      = dictAtIndices(failures),
                       x         = 'size',
                       y         = 'time',
                       size      = cross['size'],
                       edgecolor = 'k',
                       linewidth = cross['linewidth'],
                       marker    = 'x',
                       color     = 'r',
                       ax        = ax)
    ax = sns.swarmplot(data      = dictAtIndices(successes),
                       x         = 'size',
                       y         = 'time',
                       size      = point['size'],
                       edgecolor = 'k',
                       linewidth = point['linewidth'],
                       marker    = 'o',
                       color     = 'k',
                       ax        = ax)
    #ax.set_xlim(1, 20)  # Force X limits in case success and fail differ

    #ax.set_xlim(1, 20)  # Force X limits in case success and fail differ
    if ax.legend_: ax.legend_.remove()
    ax.set_xlabel('Sample size')
    ax.set_ylabel('Runtime (seconds)')

    savePlot('quickspectime')
plotQSTime()
del(plotQSTime)

def plotICSTime():
    agg = aggs['isacosy']
    fig = newFigure('time')
    ax  = fig.gca()
    plt.ylim(0, 300)
    sns.plt.xlim(1, 20)

    sns.boxplot(data      = agg,
                     x         = 'size',
                     y         = 'time',
                     color     = '0.95',
                     fliersize = 0,
                     ax        = ax)

    # Alternatively, we could use stripplot with jitter
    successes = [i for i,s in enumerate(agg['success']) if     s]
    failures  = [i for i,s in enumerate(agg['success']) if not s]
    listAtIndices = lambda idc, lst: [x for i,x in enumerate(lst) if i in idc]
    dictAtIndices = lambda idc, f=lambda x: x, g=lambda x: x: dict(agg,
                                     size=map(f,listAtIndices(idc, agg['size'])),
                                     time=map(g,listAtIndices(idc, agg['time'])))

    ax = plt.gca()
    ax.set_xlim(0, 19)  # Force X limits in case success and fail differ
    ax = sns.swarmplot(data      = dictAtIndices(successes),
                       x         = 'size',
                       y         = 'time',
                       size      = point['size'],
                       edgecolor = 'k',
                       linewidth = point['linewidth'],
                       marker    = 'o',
                       color     = 'k',
                       ax        = ax)

    # IsaCoSy had no failures for size 1, so seaborn (in its infinite wisdom)
    # will end up plotting things offset from each other and lying about the
    # x-axis. Urgh. To avoid this, we add a fake failure at x position 1, so
    # that the failures span the whole 1-20 range. We hide the point by giving
    # it a negative y position, so it drops off the bottom of the chart.
    fails          = dictAtIndices(failures)
    fails['size'] += [1]
    fails['time'] += [-10]

    ax = sns.swarmplot(data      = fails,
                       x         = 'size',
                       y         = 'time',
                       size      = cross['size'],
                       linewidth = cross['linewidth'],
                       marker    = 'x',
                       color     = 'r',
                       ax        = ax)

    if ax.legend_: ax.legend_.remove()
    ax.set_xlabel('Sample size')
    ax.set_ylabel('Runtime (seconds)')

    savePlot('isacosytime')
plotICSTime()
del(plotICSTime)

for system in aggs:
    plotPrecRec(system, aggs[system])
