#! /usr/bin/env nix-shell
#! nix-shell -i bash -p xidel bash

# Find the most popular Haskell packages which use property testing
# We find the reverse dependencies of some property checkers, find the most
# downloaded Haskell packages, and take the intersection

function reverse_deps {
    xidel --extract '//table//td[not(@class="version")]' "http://packdeps.haskellers.com/reverse/$1"
}

function check_deps {
    for PKG in QuickCheck smallcheck lazysmallcheck sparsecheck
    do
        reverse_deps "$PKG"
    done
}

function top_packages {
    xidel --extract '//table//tr/td/a/text()' "http://hackage.haskell.org/packages/top" 2> /dev/null
}

function top_tests {
    DEPS=$(check_deps)
    while read -r PKG
    do
        [[ -z "$PKG" ]] && continue
        while read -r DEP
        do
            [[ "x$PKG" = "x$DEP" ]] && {
                echo "$PKG"
                break
            }
        done < <(echo "$DEPS")
    done < <(top_packages)
}

# Take the top 10
head -n10 < <(top_tests)
