{ pkgs, coqpyt-src }:
let
  coqpyt = pkgs.python3Packages.buildPythonPackage rec {
    pname = "coqpyt";
    version = "0.0.1";
    src = coqpyt-src;
  };
in
with pkgs;
[
  jupyter
  uv
  (python312.withPackages (
    ps: with ps; [
      alectryon
      coqpyt
    ]
  ))
]
