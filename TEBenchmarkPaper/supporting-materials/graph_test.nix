# Experiments with Matplotlib and Seaborn, to discover and demonstrate how their
# functionality does and doesn't work.
#
# NOTE TO SELF: Never use Seaborn again: it's under-documented, dangerous
# (produces incorrect plots with no indication that this has happened) and the
# developer is actively hostile.
with (import ../../resources).nixpkgs.nixpkgs1609;
with { py = python.withPackages (p: [ p.matplotlib p.seaborn ]); };
runCommand "graph_test"
  {
    buildInputs = [ py ];
    script      = writeScript "graph_test.py" ''
      #!${py}/bin/python
      import matplotlib        as mpl
      import numpy             as np
      import matplotlib.pyplot as plt
      import seaborn           as sns

      def box(ax):
        return sns.boxplot(data      = {'x':[1,2,3], 'y':[101,102,103]},
                           x         = 'x',
                           y         = 'y',
                           color     = '0.95',
                           fliersize = 0,
                           ax        = ax)

      def swarm(ax):
        return sns.swarmplot(data      = {'x':[1,2,3,4], 'y':[200,202,203,204],'h':["FFFFFF00","000000FF","000000FF","000000FF"]},
                             x         = 'x',
                             y         = 'y',
                             hue       = 'h',
                             size      = 3,
                             edgecolor = 'k',
                             linewidth = 1,
                             marker    = 'o',
                             color     = 'k',
                             ax        = ax)

      def boxSwarm(ax):
        return swarm(box(ax))

      def swarmBox(ax):
        return box(swarm(ax))

      for n,f in [('swarm',swarm),
                  ('box'  ,box  ),
                  ('boxswarm', boxSwarm),
                  ('swarmbox', swarmBox)]:
        fig = plt.figure(figsize=(6, 6))
        ax  = fig.gca()
        # ax  = fig.gca()
        #ax.set_autoscale_on(False)
        # plt.ylim(0, 300)
        # plt.xlim(1, 20)
        # sns.plt.xlim(1, 20)
        f(ax)
        plt.tight_layout()
        plt.savefig(n + '.png', bbox_inches='tight', pad_inches=0.0)
    '';
  }
  ''
    mkdir "$out"
    cd "$out"
    "$script"
  ''
