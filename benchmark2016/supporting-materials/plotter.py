#!/usr/bin/env python
import sys
import matplotlib
import numpy as np
import matplotlib.pyplot as plt
import json
import random

def time_of(r):
    """Return the time taken by a benchmark; 0 if it failed."""
    return field_of(r, "time", 0)

def field_of(r, field, default):
    return r[field] if r["failure"] is None else default

def draw_bar(data, mode, size):
    """Draw a bar chart of `data`; `mode` and `size` are for labels."""
    print(repr((data, mode, size)))
    N = len(data)
    x = range(N)
    if all([val == 0 for val in data]):
        sys.stderr.write("All datapoints 0\n")
        sys.stderr.write("Skipping plot to avoid MatPlotLib errors\n")
    else:
        plt.bar(x, data, width=1/1.5, color="blue", log=True)
    plt.title("Sample size %s, %s" % (size, mode))

def draw_bars(times, shuffled, size):
    """Draw one bar chart for `times` and one for `shuffled`. Put next to
    each other for easy comparison."""
    plt.figure(figsize=(8, 6))

    # Write the ordered times
    plt.subplot(2, 1, 1)
    draw_bar(times, "ordered", size)

    # Write the shuffled times
    plt.subplot(2, 1, 2)
    draw_bar(shuffled, "shuffled", size)

    plt.savefig("bars-%s.png" % size)

def lag_plot(lag, times, mode, size):
    """Draw a lag plots for the `times` series."""
    plt.plot(times[lag:], times[:-1*lag], 'kx')
    plt.title("Lag %s, sample size %s, %s" % (lag, size, mode))

def lag_plots(times, shuffled, size):
    """Draw 4 lag plots for `times` and `shuffled`."""
    plt.figure(figsize=(12, 24))
    plot_num = 0
    for lag in [1,2,3,4]:
        plot_num += 1
        plt.subplot(4, 2, plot_num)
        lag_plot(lag, times, "ordered", size)

        plot_num += 1
        plt.subplot(4, 2, plot_num)
        lag_plot(lag, shuffled, "shuffled", size)
    plt.savefig("lag-%s.png" % size)

def correlation(data, mode, size):
    """Plot the autocorrelation function for `data`."""
    if len(data) > 1:
        # Lift any integers to floats, so division won't truncate
        float_data = map(float, data)

        # Normalise our data, ready for autocorrelation. Begin by subtracting
        # the mean, so that our data becomes centred about zero.
        centred_data = [x - np.mean(float_data) for x in float_data]

        # Shrink the data such that it has a unit norm: we calculate the norm
        # (`ord=1` for L1 norm, `ord=2` for L2 norm, etc.), then divide each
        # element by this value (or an appropriate epsilon, if the norm is 0).
        normed_data = np.divide(centred_data,
                                max(np.linalg.norm(centred_data, ord=2),
                                    sys.float_info.epsilon))

        plt.acorr(normed_data,
                  maxlags=None, usevlines=True, normed=True, lw=2)

    plt.title("Autocorrelation, sample size %s, %s" % (size, mode))

def correlations(times, shuffled, size):
    """Plot autocorrelation for ordered and shuffled series."""
    plt.figure(figsize=(12, 3))

    axis = plt.subplot(1, 2, 1)
    axis.set_xbound(lower=-0.5)
    correlation(times, "ordered", size)

    axis = plt.subplot(1, 2, 2)
    axis.set_xbound(lower=-0.5)
    correlation(shuffled, "shuffled", size)
    plt.savefig("acorr-%s.png" % size)

def main(data):
    '''For each run of data, render an ordered figure and a shuffled figure.'''
    sizes = [r["info"] for r in data]
    for index, run in enumerate(data):
        times = map(time_of, run["results"])

        # Shuffle a copy of the times. Use fixed seed for reproducibility.
        shuffled = [x for x in times]
        random.Random(42).shuffle(shuffled)

        for f in (draw_bars, lag_plots, correlations):
            f(times, shuffled, sizes[index])

        precisions = [{"mean"   : np.mean([field_of(r, "precision", 0)
                                           for r in run["results"]]),
                       "stddev" : np.std([field_of(r, "precision", 0)
                                          for r in run["results"]])}
                      for run in data]
        recalls    = [{"mean"   : np.mean([field_of(r, "recall", 0)
                                           for r in run["results"]]),
                       "stddev" : np.std([field_of(r, "recall", 0)
                                          for r in run["results"]])}
                      for run in data]
        print(repr({"precisions":precisions,"recalls":recalls}))

if __name__ == '__main__':
    main(json.loads(sys.stdin.read()))
