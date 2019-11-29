#!/usr/bin/env python3
import sys
def err(x):
    sys.stderr.write(x + '\n')
    sys.stderr.flush()

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

def justTotals(rep):
    '''Count how many theorems were found for each method and count; discard the
    actual names, to save space.'''
    theorems = len(rep['sampleTheorems'])
    result   = {'size': rep['size'], 'theorems':theorems}
    for method in rep['bucketed']:
        result[method] = {}
        for count in rep['bucketed'][method]:
            result[method][count] = \
                len(rep['bucketed'][method][count]['theorems'])
    return result

# Read all reps, keeping just the proportion of theorems for each bucketing
sizes = {}
for rep in genReps():
    if rep['size'] not in sizes:
        sizes[rep['size']] = []
    sizes[rep['size']].append(justTotals(rep))

from os import getenv
r = getenv('wilcoxon')
del(getenv)

i2b = lambda i: bytes(str(i), encoding='utf-8')

def wilcoxon(given):
    '''Perform Wilcoxon signed rank test. The SciPy version isn't exact, so we
    call out to R (urgh). To keep down overheads, we make one call containing
    all of our data, rather than one per test.'''

    # This will contain our results; initially with dummy sentinel values, then
    # filled in based on the results
    pValues = []

    # This contains the lines of text to send into R's stdin
    data = []

    for label in given:
        old = given[label]['old']
        new = given[label]['new']

        # We can only do the test if there are some differences
        if all([x == y for (x, y) in zip(old, new)]):
            # No differences found, so we don't sent this to R. We still need to
            # keep track of it in pValues, to ensure it's skipped when reading
            # results back
            pValues.append({'label':label, 'skip':True})
        else:
            # We have some differences, to we can send these values into R, and
            # we should expect a p-value back.
            pValues.append({'label':label, 'skip':False})
            with open(label + '.csv', 'w') as f:
                for o, n in zip(old, new):
                    f.write(','.join([str(o), str(n)]) + '\n')
            data.append((label + '.csv'))

    # To avoid problems looping over stdin in R, we write filenames to a file
    with open('filenames', 'w') as f:
        f.write('\n'.join(data))

    # Invoke R once, bailing out if it throws an error
    import subprocess
    result = subprocess.run([r],  # This is our R script, read from an env var
                            check=True,
                            stdout=subprocess.PIPE)

    # Extract every p-value from result, and assign each to the labels we expect
    index = 0
    for line in result.stdout.decode('utf-8').split('\n'):
        if line.strip() == '':
            continue

        assert index < len(pValues), repr({
            'error'  : 'Too many p-value matches',
            'index'  : index,
            'pValues': len(pValues),
            'line'   : line
        })

        # Ignore entries which had no differences, and hence weren't sent to R
        while pValues[index]['skip']:
            index += 1
        pValues[index]['pvalue'] = line.strip()
        index += 1

    # Format the return value
    formatted = {}
    for pValue in pValues:
        if pValue['skip']:
            assert 'pvalue' not in pValue, repr({
                'error': 'Skipped entry should not have p-value',
                'data' : pValue
            })
            formatted[pValue['label']] = None
        else:
            assert 'pvalue' in pValue, repr({
                'error': 'Non-skipped entry does not have p-value',
                'data' : pValue
            })
            formatted[pValue['label']] = pValue['pvalue']

    return formatted

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
counts     = sorted(list(sizes.values())[0][0]['hashed'].keys())
paired     = {}
toWilcoxon = {}  # Gather up data to send into R
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
                paired[size][count] = {
                    'hashed'   :[],
                    'recurrent':[],
                    'proportions':{
                        'hashed'   :[],
                        'recurrent':[]
                    }}
            for method in ['hashed', 'recurrent']:
                paired[size][count][method].append(rep[method][count])
                paired[size][count]['proportions'][method].append(
                    rep[method][count] / rep['theorems'])

    for count in paired[size]:
        data         = paired[size][count]

        toWilcoxon[str(size)+'_'+str(count)] = {
            'old':data['hashed'   ],
            'new':data['recurrent']
        }

        mean, stddev = meanStdDev([r - h for r, h in zip(
            data['proportions']['recurrent'],
            data['proportions']['hashed'   ])])
        paired[size][count].update({
            'meandelta' : mean,
            'stddev'    : stddev,
        })

# Add Wilcoxon test results
wilcoxoned = wilcoxon(toWilcoxon)
del(toWilcoxon)
for label in wilcoxoned:
    size, count = label.split('_')
    paired[size][count]['wilcoxon'] = wilcoxoned[label]

del(sizes)

import json
print(json.dumps(paired))
