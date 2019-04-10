#!/usr/bin/env python3
from os  import getenv
from csv import DictReader

def msg(x):
    from sys import stderr
    stderr.write(repr(x))
    stderr.flush()

def save(name, axes):
    axes.get_figure().savefig(name + '.pdf')
    axes.get_figure().savefig(name + '.pgf')

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
save('contents', plt.gca())
