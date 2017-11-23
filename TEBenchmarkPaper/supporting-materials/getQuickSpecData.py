#!/usr/bin/env python
import sys
msg = sys.stderr.write

msg('Reading in the page width we calculated from TeX\n')
import os
with open(os.getenv('textWidth'), 'r') as textWidthFile:
  textWidthPt = float(textWidthFile.read())

# Must be done before importing matplotlob.pyplot
# Taken from http://bkanuka.com/articles/native-latex-plots
msg('Setting matplotlib latex output\n')
import matplotlib as mpl
import numpy      as np

def figSize(widthFraction, height=None):
  ptToInch    = 1.0 / 72.27
  textWidthIn = textWidthPt * ptToInch
  goldMean    = (np.sqrt(5.0)-1.0) / 2.0
  calcWidth   = widthFraction * textWidthIn
  calcHeight  = textWidthIn * ((goldMean * widthFraction) \
                               if height is None else height)
  return (calcWidth, calcHeight)

pgf_with_latex = {
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
}
mpl.rcParams.update(pgf_with_latex)

import matplotlib.pyplot as plt
import seaborn           as sns

get = lambda x, *path: x if path == () else get(x[path[0]], *path[1:])
num = lambda x: type(x) in [type(42), type(42.0)]

msg('Gathering input\n')
import gzip
import json
with gzip.open(os.getenv('zipped'), 'r') as zipped:
  data = get(json.load(zipped),
             'results', 'quickspectip.track_data', 'result', 0)

agg = {
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

# Make a note of which equations are discoverable from each sample
knownEqs = {}

for size in sorted(map(int, data.keys())):
  msg('Extracting data for size {0}\n'.format(size))
  sdata = data[str(size)]['reps']
  for rep in sorted(map(int, sdata.keys())):
    rdata = sdata[str(rep)]

    sample = frozenset(rdata['sample'])
    assert len(sample) == size, repr({
      'error' : 'Wrong number of names sampled',
      'rep'    : rep,
      'sample' : rdata['sample'],
      'size'   : size
    })
    assert len(sample) == len(rdata['sample']), repr({
      'error'  : 'Duplicate names sampled',
      'rep'    : rep,
      'sample' : rdata,
      'size'   : size
    })

    got = frozenset(rdata['found'][0]) if rdata['success'] else None
    for known in knownEqs:
      if sample.issubset(known) and got and known[knownEqs]:
        assert got.issubset(knownEqs[known]), repr({
          'error' : 'Subset not found',
          'size'  : size,
        })
    if sample in knownEqs:
      prev = knownEqs[sample]
      assert prev == got, repr({
        'error'  : 'Differing outputs for duplicate samples',
        'prev'   : prev,
        'rep'    : rep,
        'sample' : got,
        'size'   : size
      })

      msg('Size {0} rep {1} is a dupe, skipping\n'.format(
        size, rep))
    else:
      knownEqs[sample] = got

      found  = len(got)             if rdata['success'] else 0
      wanted = len(rdata['wanted']) if rdata['success'] else 0

      # Get the time if available, otherwise treat as a timeout
      # We use min since killing might take some time
      t = min(rdata['time'], rdata['timeout'])
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
      agg['found'    ].append(found)
      agg['precision'].append(p)
      agg['precHue'  ].append(wanted + 1 if rdata['success'] else 0)
      agg['recall'   ].append(r)
      agg['recHue'   ].append(wanted + 1 if rdata['success'] else 0)
      agg['size'     ].append(size)
      agg['time'     ].append(t)
      agg['timeHue'  ].append(found  + 1 if rdata['success'] else 0)
      agg['wanted'   ].append(wanted)

from matplotlib.colors import ListedColormap
foundMax  = max(agg['found'])
foundMap  = sns.color_palette('viridis', foundMax + 1).as_hex()
foundMap2 = dict(enumerate(['#ff0000'] + foundMap))
lfoundMap = ListedColormap(foundMap)
foundNorm = mpl.colors.Normalize(vmin=0, vmax=foundMax)
msg('Highest conjecture count is {0}\n'.format(foundMax))

wantedMax  = max(agg['wanted'])
wantedMap  = sns.color_palette('viridis', wantedMax + 1).as_hex()
wantedMap2 = dict(enumerate(['#ff0000'] + wantedMap))
lwantedMap = ListedColormap(wantedMap)
wantedNorm = mpl.colors.Normalize(vmin=0, vmax=wantedMax)
msg('Highest ground truth count is {0}\n'.format(wantedMax))

def plotTime():
  timeWidthFraction  = float(os.getenv('timeWidthFraction'))
  timeHeightFraction = float(os.getenv('timeHeightFraction'))
  plt.figure(figsize=figSize(timeWidthFraction, timeHeightFraction))
  sns.set_style('whitegrid')
  sns.set_context('paper')
  plt.ylim(0, 180)

  sns.boxplot(data      = agg,
              x         = 'size',
              y         = 'time',
              color     = '0.95',
              fliersize = 0)
  # Alternatively, we could use stripplot with jitter
  ax = sns.swarmplot(data      = agg,
                     x         = 'size',
                     y         = 'time',
                     size      = 2,  # Marker size
                     edgecolor = 'k',
                     linewidth = 0.3,
                     palette   = foundMap2,
                     hue       = 'timeHue')

  # Paraphenalia
  ax.legend_.remove()
  ax.set_xlabel('Sample size')
  ax.set_ylabel('Runtime (seconds)')

  # Add colorbar to show conjecture count
  cbax, kw = mpl.colorbar.make_axes_gridspec(
               ax,
               orientation = 'horizontal',  # Keeps plot full width
               pad         = 0.18)          # 0.15 would cover x-label
  cbar     = mpl.colorbar.ColorbarBase(cbax,
                                       cmap = lfoundMap,
                                       norm = foundNorm,
                                       **kw)
  cbar.set_label('Conjectures found')

  plt.tight_layout()
  plt.savefig('time.pgf', bbox_inches='tight', pad_inches=0.0)

def plotPrecRec():
  precRecWidthFraction  = float(os.getenv('precRecWidthFraction'))
  precRecHeightFraction = float(os.getenv('precRecHeightFraction'))
  width, height = figSize(precRecWidthFraction, precRecHeightFraction)

  # Make a new figure, but width/height need to be set after subplots
  plt.figure()
  sns.set_style('whitegrid')
  sns.set_context('paper')

  fig, (precAx, recAx) = plt.subplots(nrows=2)
  fig.set_figwidth(width)
  fig.set_figheight(height)

  map(lambda ax: ax.set_ylim(0, 1), [precAx, recAx])

  # Alternatively, we could use stripplot with jitter
  precAx = sns.swarmplot(data    = agg,
                         x       = 'size',
                         y       = 'precision',
                         hue     = 'precHue',
                         size    = 2,  # Marker size
                         palette = wantedMap2,
                         ax      = precAx)

  recAx = sns.swarmplot(data    = agg,
                        x       = 'size',
                        y       = 'recall',
                        hue     = 'recHue',
                        size    = 2,  # Marker size
                        palette = wantedMap2,
                        ax      = recAx)

  # Paraphenalia
  precAx.legend_.remove()
  precAx.set_xlabel('Sample size')
  precAx.set_ylabel('Precision')

  recAx.legend_.remove()
  recAx.set_xlabel('Sample size')
  recAx.set_ylabel('Recall')

  plt.tight_layout()
  plt.savefig('prec.pgf', bbox_inches='tight', pad_inches=0.0)

plotTime()
plotPrecRec()
