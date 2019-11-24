#!/usr/bin/env python3
from os  import getenv
from csv import DictReader

label       = getenv('name')
textWidthPt = float(getenv('textWidth'))

def msg(x):
    from sys import stderr
    stderr.write(repr(x))
    stderr.flush()

from math import sqrt

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
    counts = DictReader(f)
    rows   = [{**row,
               **{'successes': int(row['successes']),
                  'failures' : int(row['failures' ])}} for row in counts]

del(getenv    )
del(DictReader)

rows.sort(key=lambda x: x['successes'] / (x['successes'] + x['failures']),
          reverse=True)

names     = [row['name'     ] for row in rows]
successes = [row['successes'] for row in rows]
failures  = [row['failures' ] for row in rows]

# Store how many names we found, so it can be spliced into the document
with open('proportions_graph_count_' + label + '.tex', 'w') as f:
    f.write(str(len(names)))

prop = lambda key: lambda row: row[key] / (row['successes'] + row['failures'])

successProp = list(map(prop('successes'), rows))
failureProp = list(map(prop('failures' ), rows))

import matplotlib.pyplot as plt

r    = [x for x in range(0, len(names))]
plot = lambda color, prop, **kwargs: plt.bar(r, prop,
                                             color=color, edgecolor='none',
                                             width=0.5, **kwargs)

plot('#00ff00', successProp                    )
plot('#ff0000', failureProp, bottom=successProp)
del(plot)

# Custom x axis
plt.xticks([])
plt.xlim(-0.5, len(names)-0.5)  # https://stackoverflow.com/a/46798215/884682
plt.xlabel("Definition")

plt.ylim(0.0, 1.0)
plt.ylabel('Halt/timeout ratio')

save('proportions', plt.gca(), size=(0.72, 0.72))
