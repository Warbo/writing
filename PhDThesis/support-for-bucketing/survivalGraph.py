#!/usr/bin/env python3

from os     import getenv
from pandas import read_csv
with open(getenv('csv'), 'r') as f:
    times = read_csv(f, header=0, index_col=0)
del(read_csv)

label       = getenv('label')
textWidthPt = float(getenv('textWidth'))
del(getenv)

from math import sqrt

def figSize(widthFraction, height=None):
    ptToInch    = 1.0 / 72.27
    textWidthIn = textWidthPt * ptToInch
    goldMean    = (sqrt(5.0)-1.0) / 2.0
    calcWidth   = widthFraction * textWidthIn
    calcHeight  = textWidthIn * ((goldMean * widthFraction) \
                                 if height is None else height)
    return (calcWidth, calcHeight)

from lifelines import KaplanMeierFitter
import matplotlib.pyplot as plt

def save(name, axes, size=None):
    fig = axes.get_figure()
    if size is not None:
        (w, h) = size
        fig.set_size_inches(figSize(w, h))
    fig.savefig(name + label + '.pdf')
    fig.savefig(name + label + '.pgf')

axes = plt.subplot(111, label="stepped")
kmf  = KaplanMeierFitter()
for s, grouped_df in times.groupby('size'):
    if s not in [1, 5, 10, 15, 20]:
        continue
    kmf.fit(grouped_df['time'], grouped_df['success'], label=str(s))
    axes = kmf.plot(ax=axes)
save('stepped', axes)

def crossValidate(name, fitter):
    from lifelines.utils import k_fold_cross_validation
    import numpy as np
    print("Cross Validating " + name)
    print(np.mean(k_fold_cross_validation(fitter,
                                          times,
                                          duration_col='time',
                                          event_col='success')))
    print("End cross-validation of " + name)

from lifelines import CoxPHFitter
cph = CoxPHFitter()
cph.fit(times, duration_col='time', event_col='success', show_progress=True)

cph.print_summary()

save('coxph', cph.plot())
#cph.check_assumptions(times, show_plots=True)

crossValidate('cox', cph)

fitters = {'cox':cph}

from lifelines import WeibullAFTFitter, LogNormalAFTFitter, LogLogisticAFTFitter
for (name, fitter) in [("weibull"    , WeibullAFTFitter    ),
                       ("lognormal"  , LogNormalAFTFitter  ),
                       ("loglogistic", LogLogisticAFTFitter)]:
    print("BEGIN " + name)
    aft = fitter()
    aft.fit(times, duration_col='time', event_col='success')
    aft.print_summary(3)

    #aft = WeibullAFTFitter().fit(times, 'time', 'success', ancillary_df=True)
    save(name + 'aft', aft.plot())
    fitters[name] = aft
    crossValidate(name, aft)
    print("END " + name)

print('EXAMPLE DATA FOLLOWS')
from lifelines import AalenAdditiveFitter, CoxPHFitter
from lifelines.datasets import load_regression_dataset
from lifelines.utils import k_fold_cross_validation
import numpy as np

df = load_regression_dataset()

#create the three models we'd like to compare.
aaf_1 = AalenAdditiveFitter(coef_penalizer=0.5)
aaf_2 = AalenAdditiveFitter(coef_penalizer=10)
cph = CoxPHFitter()


print(np.mean(k_fold_cross_validation(cph, df, duration_col='T', event_col='E')))
print(np.mean(k_fold_cross_validation(aaf_1, df, duration_col='T', event_col='E')))
print(np.mean(k_fold_cross_validation(aaf_2, df, duration_col='T', event_col='E')))
