{ onlyPdf ? true }:
with {
  support = import ./supporting-materials {
    inherit (import ../resources) bibtex nixpkgs;
  };
};
if onlyPdf
   then support.render {}
   else support
