with { inherit (import ../resources) bibtex nixpkgs; };
with nixpkgs;
with lib;
with {
  tex = (texlive.combine {
    inherit (texlive) helvetic paralist scheme-small tikz-qtree;
  });
};

attrsToDirs' "PhDSymposium2016" {
  "abstract.pdf" = runCommand "phd-symposium-2016-abstract.pdf"
    {
      inherit bibtex;
      buildInputs = [ pandocPkgs tex ];
      render      = writeScript "render" ''
        #!${bash}/bin/bash
        set -e
        pdflatex -interaction=nonstopmode -halt-on-error --shell-escape abstract
      '';
    }
    ''
      ${concatStringsSep "\n" (map (f: ''ln -s "${./. + "/${f}"}" ./${f}'') [
        "abstract.tex" "sig-alternate.cls" "templates"
      ])}

      cp "$bibtex" Bibtex.bib

      "$render"
      bibtex abstract
      "$render"
      "$render"

      mv abstract.pdf "$out"
    '';

  "slides.html" = runCommand "phd-symposium-2016-slides.html"
    {
      buildInputs = [ ditaa ghostscript imagemagick pandocPkgs tex ];
      LANG        = "en_US.UTF-8";
    }
    ''
      pandoc -t slidy --standalone --self-contained --filter pandoc-citeproc \
             --filter panpipe --filter panhandle -o "$out" "${./slides.md}"
    '';
}
