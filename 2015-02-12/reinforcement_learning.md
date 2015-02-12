---
title: Reinforcement Learning for Proof Automation
bibliography: /home/chris/Documents/ArchivedPapers/Bibtex.bib
---

The **reinforcement learning** (RL) problem builds on the general **agent/environment** framework; a simplifying assumption used in many AI fields [@Russell:2003:AIM:773294]. In an agent/environment setup, the **agent** (the learning system) is distinct from the **environment** (everything else), and all interaction is via discrete, alternating messages between the two; known as **actions** (from agent to environment) and **observations** (from environment to agent):

```{pipe="dot -Tpng -o ae.png"}
digraph {
  rankdir="LR"
  dpi="256"
  Agent -> Environment [label="Actions"]
  Agent -> Environment [style="invis"]
  Environment -> Agent [label="Observations"]
}
```

```{.unwrap pipe="sh | pandoc -f html -t json"}
echo '<img src="data:image/png;base64,'
base64 < ae.png
echo '" alt="Agent/environment framework" />'
```

Reinforcement learning [@Sutton:1998:IRL:551283] forces all observations to be paired with a **reward**:

```{pipe="dot -o rl.png -Tpng"}
digraph {
  rankdir="LR";
  dpi="256"
  Agent -> Environment [label="Actions"]
  Agent -> Environment [style="invis"]
  Environment -> Agent [label="Reward & Observation"]
}
```

```{.unwrap pipe="sh | pandoc -f html -t json"}
echo '<img src="data:image/png;base64,'
base64 < rl.png
echo '" alt="Reinforcement learning framework" />'
```

Rewards must admit a total order, which the agent uses to distinguish how well it is performing, but are otherwise unconstrained. Specific problem instances may use a very limited reward signal like $\left\{ {0,1} \right\}$ to indicate success/failure, or a rich space like $\mathbb{R}$ to encode some performance metric. Agents choose their actions to maximise their **goal**; for example, maximising the expectation of a large reward or maximising the expected sum of future rewards (if the reward type admits addition).

## Reinforcement Learning and Games ##

The agent/environment interaction and notion of reward make reinforcement learning a very general form of *game*. This makes RL amenable to study via game theory, but also as a model of existing, real games. For example, Samuel's Checkers-playing programs [@samuel1960programming] use an approach which would today be labelled reinforcement learning. Remarkably, this connection runs both ways: state-of-the-art Go-playing programs like MoGo [@lee2009computational] are based on *Monte-Carlo tree search* algorithms (MCTS) such as *upper confidence trees* (UCT). This success has inspired the application of MCTS to the *general* reinforcement learning problem; for example the MC-AIXI-CTW algorithm [@veness2011monte] is based on a Monte Carlo *context tree weighting* algorithm, and has been applied to many RL domains without modification.

### Theorem Proving and Games ###

The act of theorem proving can be considered as a one-player game, where proof assistants can be used to enforce the rules. This is most obvious in tactic-based assistants like Coq, which explicitly reify goals and strategies, turning programming tasks into a sequence of puzzles.

## Learning Benchmarks ##

Modern RL agents are capable of operating in increasingly sophisticated domains, so require equally sophisticated methods for measuring and comparing their relative performance. One popular benchmark is the *Arcade Learning Environment* [@DBLP:journals/jair/BellemareNVB13], which has agents play a number of real computer games on an emulated Atari2600.

# References #
