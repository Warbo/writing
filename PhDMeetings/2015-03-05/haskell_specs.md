---
title: Specification Tools for Haskell
---

Reliability of software is an important concern as the modern world increasingly depends, in increasingly critical ways, on *more* software and *more complex* software.

There are many approaches to ensuring reliability, some of which overlap and some of which are orthogonal. The techniques described here are, somewhat artificially, arranged on the following scale:

```{pipe="cat > fig1.ditaa"}
/-------------------\
|      Nothing      | | H
|-------------------| | e
|  Manual testing   | | l
|-------------------| | l
| Automated testing | | o
|-------------------| |
| Property checking | |
|-------------------| V
\-------------------/
```

```{.unwrap pipe="sh | pandoc -f html -t json"}
ditaa fig1.ditaa > /dev/null
echo '<img src="data:image/png;base64,'
base64 < fig1.png
echo '" alt="fig1" />'
```
