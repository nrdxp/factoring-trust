let
  pkgs = import (builtins.fetchTarball {
    url = "https://github.com/nixos/nixpkgs/archive/fb7944c166a3b630f177938e478f0378e64ce108.tar.gz";
    sha256 = "sha256:1k5rlkipyc4n7jk8nfmzm1rg3i94zmr90k41yplxhnrb3fkk808j";
  }) { };
in
with pkgs;
mkShell {
  packages = [
    # Whitepaper rendering (docs/paper/) — the Lean model itself builds via
    # elan/lake (lean-toolchain), out of scope for this shell.
    quarto
    (texlive.combine {
      # ieeetran added beyond eml's set: the paper moved from a vendored
      # usenix.sty to IEEEtran.cls/IEEEtranN.bst, which scheme-medium alone
      # does not provide.
      #
      # tcolorbox/fontawesome5 added: Quarto's PDF callout blocks (used for
      # the working-draft banner in index.qmd) render via tcolorbox with a
      # fontawesome5 icon; neither ships in scheme-medium.
      #
      # framed added: template.tex carries Pandoc's $highlighting-macros$,
      # whose Shaded environment is built on framed.sty. Without it the
      # placeholder is a trap — present, so listings look supported, but the
      # first highlighted block fails the build. The paper has no listing
      # today; this makes the placeholder honest rather than latent.
      inherit (texlive)
        scheme-medium pgfplots standalone tools ieeetran
        tcolorbox fontawesome5 environ pgfopts tikzfill pdfcol framed;
    })
  ];
}
