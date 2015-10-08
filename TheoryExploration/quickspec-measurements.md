---
title: QuickSpec Measurements
---

<!-- Split apart Hoogle output "module name :: type1 type2 ..." -->

```{pipe="sh"}
PRELUDE=$(cd root/hoogle;
          hoogle "[a] +Prelude" | grep "^Prelude " | grep -v "IO")
echo "$PRELUDE" | cut -d " " -f 2  > names
echo "$PRELUDE" | cut -d " " -f 4- > types
```

To improve the performance of QuickSpec and related tools, we need to find what the bottlenecks are and how performance varies with input.

# QuickSpec 1 #
