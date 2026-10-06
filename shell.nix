{ pkgs ? import <nixpkgs> {} }:
let
  # The Haskell toolchain is pinned to a nixpkgs revision whose ghc-9.6.7 is
  # in cache.nixos.org. The channel (nixos-26.11 as of 494ce7fd) still defines
  # haskell.compiler.ghc967 but Hydra no longer builds it, so taking it from
  # <nixpkgs> made every shell rebuild compile GHC 9.6.7 -- and a GHC 9.4.8 to
  # bootstrap it -- from source (well over an hour).
  #
  # GHC 9.6 is what stack.yaml's lts-22.9 snapshot needs. The C libraries GHC
  # links against come from the same pin, so compiled binaries and
  # LD_LIBRARY_PATH agree on one glibc; everything else follows the channel.
  #
  # To move off the pin: bump the resolver to a snapshot whose GHC the channel
  # caches (check with `nix path-info --store https://cache.nixos.org
  # $(nix-instantiate --eval -E 'with import <nixpkgs> {}; haskell.compiler.ghcXYZ.outPath')`).
  hsPkgs = import (fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/4975466d324710c576dc11ad614684e6bd8cad8e.tar.gz";
    sha256 = "1if9h4d8rkgd7a41j978swbixif81iqfd7hk302w0fbd23i9g7y4";
  }) {};
  nativeLibs = with hsPkgs; [ zlib gmp libffi ncurses ];
in
pkgs.mkShell {
  buildInputs = (with hsPkgs; [
    # GHC 9.6.7 — matches LTS 22.x; used as system-ghc by stack
    haskell.compiler.ghc967
    zlib.dev
    pkg-config
  ]) ++ nativeLibs ++ (with pkgs; [
    stack
    git
    cacert
    # python3 + pyyaml so the NeST_internal_docs q.py frontmatter tool runs from this shell
    (python3.withPackages (ps: [ ps.pyyaml ]))
    julia
  ]);

  LD_LIBRARY_PATH = pkgs.lib.makeLibraryPath nativeLibs;

  # Fix TLS certificate verification inside nix-shell
  SSL_CERT_FILE = "${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt";
  GIT_SSL_CAINFO = "${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt";
  CURL_CA_BUNDLE = "${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt";
}
