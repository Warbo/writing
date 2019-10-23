#!/usr/bin/env python3
from csv  import DictReader
from math import sqrt
from os   import getenv

label       = getenv('label')
textWidthPt = float(getenv('textWidth'))

def msg(x):
    from sys import stderr
    stderr.write(repr(x))
    stderr.flush()

def figSize(widthFraction, height=None):
    ptToInch    = 1.0 / 72.27
    textWidthIn = textWidthPt * ptToInch
    goldMean    = (sqrt(5.0)-1.0) / 2.0
    calcWidth   = widthFraction * textWidthIn
    calcHeight  = textWidthIn * ((goldMean * widthFraction) \
                                 if height is None else height)
    return (calcWidth, calcHeight)

def save(name, axes, size=None):
    fig = axes.get_figure()
    if size is not None:
        (w, h) = size
        fig.set_size_inches(figSize(w, h))
    fig.savefig(name + label + '.pdf', bbox_inches='tight', pad_inches=0.0)
    fig.savefig(name + label + '.pgf', bbox_inches='tight', pad_inches=0.0)

with open(getenv('csv'), 'r') as f:
    times = DictReader(f)
    rows  = [row for row in times]

del(getenv)
del(DictReader)

counts = {}
fails  = {}
for row in rows:
    s = row['size']
    if s not in counts:
        counts[s] = 0
    if s not in fails:
        fails[s] = 0
    counts[s] += 1
    if row['success'] == '0':
        fails[s] += 1

keys  = sorted(counts.keys(), key=int)
fracs = [fails[s] / counts[s] for s in keys]

msg({
    'len(fracs)': len(fracs),
    'len(range(1,21))': len(range(1,21))
})

from scipy import stats
slope, intercept, r_value, p_value, std_err = stats.linregress(range(1,21),
                                                               fracs)

import matplotlib.pyplot as plt

plt.plot(fracs, '.')

f  = lambda x: slope*x + intercept
xs = [  x  for x in range(1,21)]
ys = [f(x) for x in xs         ]

ax = plt.plot(xs, ys)

plt.xlim((1,20))
plt.ylim((0,1 ))
plt.xticks(xs)
plt.xlabel('size')
plt.ylabel('failure proportion')
save('timeouts', plt.gca(), size=(0.72, 0.72))
