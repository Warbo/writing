#!/usr/bin/env python3
import sys
err = lambda x: sys.stderr.write(x + '\n')

def genReps():
    '''Generator which yields reps parsed from stdin.
    Uses ijson to do incremental parsing, based on code from
    https://github.com/isagalaev/ijson/issues/62#issuecomment-289972061'''
    import ijson
    import ijson.common

    dotted    = lambda *args: '.'.join(args)

    sentinels = lambda size, rep: (
        size,
        rep,
        None if rep is None else dotted(size, rep),
        None if rep is None else dotted(size, rep, 'item'))

    size, rep, want, item = sentinels(None, None)

    for prefix, event, value in ijson.parse(sys.stdin):
        #print(repr({'prefix':prefix,'event':event,'value':value}))
        if prefix == '' and event == 'map_key':
            # Found a new size
            size, rep, want, item = sentinels(value, None)

        elif size is not None and prefix == size and event == 'map_key':
            # Found a new rep
            size, rep, want, item = sentinels(size, value)
            builder               = ijson.common.ObjectBuilder()

        elif want is not None and prefix.startswith(want):
            # We're still in this rep, keep building the value
            builder.event(event, value)
            if prefix == want and event == 'end_array':
                # Found the end of this rep; combine its two values
                yield {'size': size, 'rep': rep, 'bucketed': builder.value[1],
                       **builder.value[0]}

theoremProportion = lambda truth, bucket: len(bucket['theorems']) / len(truth)

def justTotals(rep):
    theorems = len(rep['sampleTheorems'])
    result   = {'size': rep['size']}
    for method in rep['bucketed']:
        result[method] = {}
        for count in rep['bucketed'][method]:
            result[method][count] = \
                len(rep['bucketed'][method][count]['theorems']) #/ theorems
    return result

# Read all reps, keeping just the proportion of theorems for each bucketing
sizes = {}
rem = 100
for rep in genReps():
    if rep['size'] not in sizes:
        rem -= 1
        if rem < 95:
            break
        err(repr(rem))
        sizes[rep['size']] = []
    sizes[rep['size']].append(justTotals(rep))

from os import getenv
r = getenv('wilcoxon')
del(getenv)

i2b = lambda i: bytes(str(i), encoding='utf-8')

import re
numRE = re.compile('[0-9][0-9.]*')
pRE   = re.compile('p-value *= *[0-9.]*')

import subprocess

def wilcoxon(old, new):
    '''Perform Wilcoxon signed rank test. The SciPy version isn't exact, so we
    call out to R (urgh).'''
    if all([x == y for (x, y) in zip(old, new)]):
        # We can't do the test if there are no differences
        return None

    csv    = b'\n'.join([i2b(x) + b',' + i2b(y) \
                         for (x, y) in zip(old, new)])
    result = subprocess.run([r],
                            input=csv,
                            check=True,
                            stdout=subprocess.PIPE)

    # Extract p-value from result
    pVal = None
    for s in pRE.findall(result.stdout):
        for n in numRE.findall(s):
            pVal = n

    return pVal

from math import sqrt
def meanStdDev(xs):
    num  = len(xs)
    mean = sum(xs) / len(xs)
    top  = sum([(x - mean)**2 for x in xs])
    frac = top / (num - 1)
    sdev = sqrt(frac)
    return (mean, sdev)

# Transpose the data so it's size->count->reps, and do Wilcoxon signed-rank test
#from scipy.stats import wilcoxon
counts = sorted(list(sizes.values())[0][0]['hashed'].keys())
paired = {}
for size in sizes:
    paired[size] = {}
    for rep in sizes[size]:
        these = sorted(rep['hashed'].keys())
        assert these == counts, repr({
            'error' : 'Unexpected bucket counts',
            'size'  : size,
            'want'  : counts,
            'got'   : these
        })
        del(these)
        for count in counts:
            if count not in paired[size]:
                paired[size][count] = {'hashed':[], 'recurrent':[]}
            for method in ['hashed', 'recurrent']:
                paired[size][count][method].append(rep[method][count])

    for count in paired[size]:
        data         = paired[size][count]
        mean, stddev = meanStdDev([r - h for r, h in zip(data['recurrent'],
                                                         data['hashed'   ])])
        paired[size][count].update({
            'wilcoxon'  : wilcoxon(data['recurrent'], data['hashed'])

            'meandelta' : mean
            'stddev'    : stddev
        })

del(sizes)

print(repr(paired))
sys.exit(1)


tested = {}
for size in deltas:
    tested[size] = {}
    for count in deltas[size]:
        tested[size][count] = wilcoxon(deltas[size][count])


print(repr(deltas['30']['5']))

exit(1)

# from pandas import read_csv
# with open(getenv('proportionsTsv'), 'r') as f:
#     times = read_csv(f, header=0, index_col=0)
# del(read_csv)

# label       = getenv('label')
# textWidthPt = float(getenv('textWidth'))
# del(getenv)

# from math import sqrt

# def figSize(widthFraction, height=None):
#     ptToInch    = 1.0 / 72.27
#     textWidthIn = textWidthPt * ptToInch
#     goldMean    = (sqrt(5.0)-1.0) / 2.0
#     calcWidth   = widthFraction * textWidthIn
#     calcHeight  = textWidthIn * ((goldMean * widthFraction) \
#                                  if height is None else height)
#     return (calcWidth, calcHeight)
