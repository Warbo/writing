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

barWidth = 0.85
r        = [x for x in range(0, len(names))]

# Create green Bars
plt.bar(r, successProp,                     color='#00ff00', edgecolor='white', width=barWidth)
# Create orange Bars
plt.bar(r, failureProp, bottom=successProp, color='#ff0000', edgecolor='white', width=barWidth)

# Custom x axis
plt.xticks(r, names)
plt.xlabel("Name")

#ax = plt.subplot(111)
#ax.bar(names, successes, width=0.3, color='g', align='center')
#ax.bar(names, failures , width=0.3, color='r', align='center')
#ax.xaxis_date()

#plt.bar([ row['name'     ]                   for row in rows],
#        [[row['successes'], row['failures']] for row in rows])

#plt.xlim((1,20))
#plt.ylim((0,1 ))
#plt.xticks(xs)
plt.xlabel('Name')
plt.ylabel('Occurrences')
plt.title('Name distribution between successful and failed runs')

#ax.set_xlabel('Name')
#ax.set_ylabel('Occurrences')
#ax.set_title('Name distribution between successful and failed runs')
save('proportions', plt.gca(), size=(0.72, 0.72))
