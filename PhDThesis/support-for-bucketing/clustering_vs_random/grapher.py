#!/usr/bin/env python3
from os import chdir, getenv, mkdir

# As proportion of textWidth
graphSize=(0.72, 0.72)

# Create the $out directory of our Nix derivation, to fill with graphs
out = getenv('out')
mkdir(out)
chdir(out)
del(chdir, mkdir)

textWidthPt = float(getenv('textWidth'))  # To scale graphs appropriately
processed   = getenv('processed') + '/out'
del(getenv)

# Read input JSON
from json import loads
data = None
with open(processed, 'r') as f:
    data = loads(f.read())
del(loads, processed)

# Extract all of the sizes and bucket counts
counts = []
sizes  = []
for size in data:
    sizes.append(int(size))
    for count in data[size]:
        counts.append(int(count))
counts = sorted(list(set(counts)))
sizes  = sorted(list(set(sizes )))

# Arrange data points into lists, which we can reference by key when plotting
points = {'size': sizes}
points.update({
    'count'+str(c): [data[str(s)][str(c)]['meandelta'] for s in sizes] \
    for c in set(counts)
})
points.update({
    'err'+str(c): [data[str(s)][str(c)]['stddev'] for s in sizes] \
    for c in set(counts)
})

# Plot each count
import matplotlib.pyplot as plt
fig = plt.figure()
ax  = fig.add_subplot(111)
for c in counts:
    ax.errorbar(data=points, x='size', y='count'+str(c), yerr='err'+str(c))
    #plt.plot('size', , data=points)

#plt.plot( 'x', 'y2', data=df, marker='', color='olive', linewidth=2)
#plt.plot( 'x', 'y3', data=df, marker='', color='olive', linewidth=2, linestyle='dashed', label="toto")

from math import sqrt
def figSize(widthFraction, height=None):
    ptToInch    = 1.0 / 72.27
    textWidthIn = textWidthPt * ptToInch
    goldMean    = (sqrt(5.0)-1.0) / 2.0
    calcWidth   = widthFraction * textWidthIn
    calcHeight  = textWidthIn * ((goldMean * widthFraction) \
                                 if height is None else height)
    return (calcWidth, calcHeight)

fig.set_size_inches(figSize(graphSize[0], graphSize[1]))
fig.savefig('foo.png', bbox_inches='tight', pad_inches=0.0)
