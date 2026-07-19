{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
  buildInputs = with pkgs; [
    # GHC 9.6.7 — matches LTS 22.x; used as system-ghc by stack
    haskell.compiler.ghc967
    stack
    git
    zlib
    zlib.dev
    gmp
    libffi
    ncurses
    pkg-config
    cacert
    # python3 + pyyaml so the NeST_internal_docs q.py frontmatter tool runs from this shell
    (python3.withPackages (ps: [ ps.pyyaml ]))
    julia
  ];

  LD_LIBRARY_PATH = pkgs.lib.makeLibraryPath (with pkgs; [ zlib gmp libffi ncurses ]);

  # Fix TLS certificate verification inside nix-shell
  SSL_CERT_FILE = "${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt";
  GIT_SSL_CAINFO = "${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt";
  CURL_CA_BUNDLE = "${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt";
}
