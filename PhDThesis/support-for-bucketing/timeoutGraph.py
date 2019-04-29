#!/usr/bin/env python3
from os  import getenv
from csv import DictReader

label = getenv('label')

def msg(x):
    from sys import stderr
    stderr.write(repr(x))
    stderr.flush()

def save(name, axes):
    axes.get_figure().savefig(name + label + '.pdf')
    axes.get_figure().savefig(name + label + '.pgf')

with open(getenv('csv'), 'r') as f:
    times = DictReader(f)
    rows  = [row for row in times]

del(getenv  )
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
plt.title('Failures as size grows')
save('timeouts', plt.gca())
#plt.savefig('timeouts.pdf')
