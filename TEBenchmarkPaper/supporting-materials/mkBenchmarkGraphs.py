#!/usr/bin/env python
from json import loads, dumps
import os
import sys
msg = lambda x: sys.stderr.write(x + '\n')

def readVar(var):
    val = os.getenv(var)
    assert val is not None, 'No {} env var given'.format(var)
    return val

sources = {
    'isacosy'   : readVar(  'ISACOSY_DATA'),
    'quickspec' : readVar('QUICKSPEC_DATA')
}
del(readVar)

msg('Reading input')

from json import load

def readInput(source, path):
    with open(sources[source], 'r') as f:
        return load(f)['results'][path]['result'][0]

data = {
    'isacosy'   : readInput('isacosy'  ,   'benchmarks.track_data'),
    'quickspec' : readInput('quickspec', 'quickspectip.track_data')
}
del(readInput)

msg('Normalising data')

# Extract timeout from one of the QuickSpec runs, since IsaCoSy didn't store it
timeout = data['quickspec'].values()[0]['reps'].values()[0]['timeout']

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

def normalise(data):
    for size in data:
        # Unwrap useless 'reps' wrapper
        if 'reps' in data[size]:
            data[size] = data[size]['reps']

        for rep in data[size]:
            # Remove more unnecessary wrappers
            for key in ['result', 'analysis']:
                if key in data[size][rep]:
                    data[size][rep] = dict(  data[size][rep],
                                           **data[size][rep][key])
                    del(data[size][rep][key])

            # Include the timeout
            if 'timeout' not in data[size][rep]:
                data[size][rep]['timeout'] = timeout

            # These are inverse, so just use one
            if 'killed' in data[size][rep] and 'success' not in data[size][rep]:
                data[size][rep]['success'] = not data[size][rep]['killed']
            if 'killed' in data[size][rep]:
                del(data[size][rep]['killed'])

            # We should always analyse, so this is useless
            if 'analysed' in data[size][rep]:
                assert data[size][rep]['analysed'], 'Run was not analysed'
                del(data[size][rep]['analysed'])

            # Remove some unneeded values, if present
            for key in ['runner', 'analyser',  # For provenance
                        'stdout', 'stderr',    # For debugging
                        'size',   'rep']:      # Violate "Once and Only Once"
                if key in data[size][rep]:
                    del(data[size][rep][key])

            # Samples should be sets
            rawSample = data[size][rep]['sample']
            sampleSet = frozenset(rawSample)
            assert len(rawSample) == int(size), \
                repr({
                    'error'     : 'Wrong number of names sampled',
                    'rep'       : rep,
                    'size'      : size,
                    'rawSample' : rawSample,
                    'sampleSet' : sampleSet
                })

            assert len(sampleSet) == len(rawSample), \
                repr({
                    'error'     : 'Sampled names contain duplicates',
                    'rep'       : rep,
                    'size'      : size,
                    'rawSample' : rawSample,
                    'sampleSet' : sampleSet
                })

            data[size][rep]['sample'] = sampleSet

            # Unwrap found to make comparable
            data[size][rep]['found'] = frozenset(
                makeHashable(data[size][rep]['found'][0]) \
                if data[size][rep]['success'] else [])

    return data

data = {
    'isacosy'   : normalise(data['isacosy'  ]),
    'quickspec' : normalise(data['quickspec'])
}

del(makeHashable)
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

                assert timeout == rdata['timeout'], \
                    'Got different timeouts {} and {}'.format(
                        str(timeout),
                        str(rdata['timeout']))

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
    needed for our graphs. Note that this needs to support JSON from QuickSpec
    and IsaCoSy, which is slightly d'''
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
        'time'      : [],
        'timeHue'   : [],
        'wanted'    : []
    }

    # Make a note of which samples we've seen before, so we can skip dupes
    knownSamples = []

    for size in sorted(map(int, data.keys())):
        msg('Extracting data for size ' + str(size))
        sdata = data[str(size)]
        for rep in sorted(map(int, sdata.keys())):
            rdata  = sdata[str(rep)]

            # QuickSpec and IsaCoSy runners have annoying differences in their
            # keys, so we glom the whole lot together
            for key in ['result', 'analysis']:
                if key in rdata:
                    rdata = dict(rdata, **rdata[key])

            sample = rdata['sample']
            got    = rdata['found']

            if sample in knownSamples:
                msg('Skipping dupe rep {0} of size {1}'.format(rep, size))
                continue

            knownSamples += [sample]

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
            agg['time'     ].append(t)
            agg['timeHue'  ].append(found  + 1 if rdata['success'] else 0)
            agg['wanted'   ].append(wanted)

    return agg

agg = {
    'isacosy'   : aggregateData(data['isacosy'  ]),
    'quickspec' : aggregateData(data['quickspec'])
}
del(data)
del(aggregateData)

msg('Setting up plots')

##FIXME
agg = agg['quickspec']

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
        'palette' : dict(enumerate(['#ff0000'] + colourMap if key == 'found' \
                                                           else colourMap))
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

def plotTime():
    newFigure('time')

    plt.ylim(0, 300)

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

def aggProp(sizes=None, agg=None, key=None, total=None):
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
        totals   = map(noneToZero, entriesOfSize(size, total))
        corrects = map(noneToZero, entriesOfSize(size, 'correct'))

        count   = sum(totals)
        correct = sum(corrects)

        p       = correct / count

        # Analytic values, calculated from our model
        anVar     = (p * (1.0 - p)) / count
        anStddev  = math.sqrt(anVar)
        anStderr  = anStddev / math.sqrt(count)

        # Sample values, calculated from our data. Variance is the average
        # squared difference between each run's actual correct proportion and
        # the correct proportion we got from the model (p).
        # Note that we filter out any runs with empty totals (i.e. we don't try
        # to work out the precision of a run which produced no conjectures)
        n       = float(len(filter(lambda x: x > 0, totals)))
        sVar    = (sum([((float(correct) / tot) - p)**2 \
                        for tot, correct in zip(totals, corrects) \
                        if  tot > 0])) / (n - 1)
        sStddev = math.sqrt(sVar)

        return {
            'mean'              : p,
            'analytic variance' : anVar,
            'analytic stddev'   : anStddev,
            'analytic stderr'   : anStderr,
            'sample variance'   : sVar,
            'sample stddev'     : sStddev
        }

    # Calculate values for graph

    analysis = ratioOfAverages

    unzip = lambda xs: zip(*xs)

    means, stdDevs = unzip([(result['mean'], result['sample stddev']) \
                            for result in map(analysis, sizes)])

    # Mean values +/- standard error
    low  = [max(0, mean - stdDev) for mean, stdDev in zip(means, stdDevs)]
    high = [min(1, mean + stdDev) for mean, stdDev in zip(means, stdDevs)]

    return means, low, high

def plotPrecRec():
    # This *should* be range(1, max), but we might as well avoid assumptions
    sizes = sorted(list(set(agg['size'])))

    # matplotlib seems to count up 0, 1, 2, ... regardless of the x label, so we
    # need to shift and scale the points
    xs = map(lambda x: (x - min(sizes)) / (sizes[1] - sizes[0]), sizes)

    precMeans, precLows, precHighs = aggProp(sizes, agg, 'precision', 'found' )
    recMeans,   recLows,  recHighs = aggProp(sizes, agg, 'recall',    'wanted')

    newFigure('precRec')
    gs            = mpl.gridspec.GridSpec(3, 1, height_ratios=[5, 5, 1])
    precAx, recAx = (plt.subplot(gs[0]), plt.subplot(gs[1]))

    map(lambda args: args['ax'].fill_between(xs, args['lows'], args['highs'],
                                             #alpha     = 0.5,
                                             facecolor = '#CCCCCC',
                                             edgecolor = 'face'),
        [{'ax': precAx, 'lows': precLows, 'highs': precHighs},
         {'ax':  recAx, 'lows':  recLows, 'highs':  recHighs}])

    drawPoints(
        ax      = precAx,
        colours = wantedColours,
        hue     = 'precHue',
        y       = 'precision',
        yLabel  = 'Precision')

    drawPoints(
        ax      = recAx,
        colours = wantedColours,
        hue     = 'recHue',
        y       = 'recall',
        yLabel  = 'Recall')

    [(ax.set_ylim(0, 1), ax.plot(xs, ms)) for ax, ms in [(precAx, precMeans),
                                                         ( recAx,  recMeans)]]

    drawColourBar(
        cax     = plt.subplot(gs[2]),
        colours = wantedColours,
        kw      = {'orientation': 'horizontal'},
        label   = 'Ground truth theorems')

    savePlot('prec')

plotTime()
plotPrecRec()
