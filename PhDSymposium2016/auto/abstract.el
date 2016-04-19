(TeX-add-style-hook
 "abstract"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("fontenc" "T1") ("inputenc" "utf8") ("hyperref" "setpagesize=false" "unicode=false" "xetex" "unicode=true")))
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperref")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperimage")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperbaseurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "nolinkurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "url")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "path")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "path")
   (TeX-run-style-hooks
    "latex2e"
    "default"
    "default10"
    "lmodern"
    "listings"
    "amssymb"
    "amsmath"
    "paralist"
    "tikz-qtree"
    "ifxetex"
    "ifluatex"
    "fixltx2e"
    "fontenc"
    "inputenc"
    "mathspec"
    "xltxtra"
    "xunicode"
    "fontspec"
    "upquote"
    "microtype"
    "hyperref")
   (TeX-add-symbols
    '("id" 1)
    '("feature" 1)
    "euro"
    "CVar"
    "CLit"
    "CApp"
    "CLam"
    "CLet"
    "CCase"
    "CType"
    "CLocal"
    "CGlobal"
    "CConstructor"
    "CLitNum"
    "CLitStr"
    "CAlt"
    "CDataAlt"
    "CLitAlt"
    "CDefault"
    "CNonRec"
    "CRec"
    "CBind")
   (LaTeX-add-labels
    "introduction"
    "background"
    "theory-exploration"
    "recurrent-clustering"
    "fig:astexample"
    "implementation"
    "results"
    "future-work")
   (LaTeX-add-bibliographies
    "../Bibtex"))
 :latex)

