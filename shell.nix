{ pkgs ? import <nixpkgs> {} }:
let
  ocaml-ps = pkgs.ocaml-ng.ocamlPackages_latest;
in
pkgs.mkShell {
  buildInputs = [
    pkgs.chicken
    ocaml-ps.ocaml
    # ocaml-ps.core
    # ocaml-ps.core_extended
    # ocaml-ps.findlib
  ];
}
