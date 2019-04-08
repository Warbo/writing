Recurrent clustering doesn't work.
We need to come up with a different narrative...

Clustering does seem to offer a tradeoff between time and available output.

We could include the median running times for different sizes. What should we
use for the variation? Median Absolute Deviation? Problem is, our cutoffs make
that biased too low :(

We can take cutoffs (censoring) into account by looking to survival rate
analysis. Some relevant-sounding topics:

 - Kaplan-Meier estimator is very popular. It estimates the survival function,
   i.e. a function of time which predicts how many runs will still be going at
   that time.
 - Survival functions can be compared using e.g. the logrank test. AFAIK this is
   a statistical test, and hence not a numerical quantity.
 - If we're willing to make more assumptions, a proportional hazards model (e.g.
   Cox) or accelerated failure time model might be more powerful, if needed.

Each of these models uses a different assumption:

 - Cox is "proportional hazards" meaning that the probability P(N) of size N
   halting each second is x*P(N+1) for some parameter x. This is similar to
   having a shorter half-life, but other distributions can be used besides
   exponential decay.

 - In an "accelerated failure" model, the parameter scales the time variable.
   For example the hazard or survival N(t) of size N at time t is (N+1)(x*t),
   i.e. it's as if smaller sizes are following the same curve but faster
   (squashed along the time axis).

From looking at our survival plots, neither of these seem to fit our case very
well. Instead, every size has a sharp drop-off at the start, leaving a roughly
flat tail; the height of this tail varies with size (tending to get higher as
the sample size increases).

How about we plot the proportion of timeouts per size?

Plot median time for different sizes, e.g. 1, 5, 10, 15, 20, with confidence
intervals (use lifelines library)

Plot recall difference for different sizes, e.g. 1, 5, 10, 15, 20. Maybe look at
log/log plots (QQ?), or otherwise just percentages. Important to be doing
pairwise difference, rather than difference of averages.

Bounds on difference plot can be min/max found via minizinc (up to size 10)

We need to compare random to clustered, and we need to set up the problem as a
useful thing to do. I think we should stick to random for the problem
description, i.e. we should plot recall difference for random, bounded by min
and max.

Separately, in a later section, we should look at pairwise-difference between
recall of random and clustered. We expect the difference to be insignificant,
but that doesn't detract from our main argument (which uses random).
