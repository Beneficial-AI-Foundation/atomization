{ inputs, ... }:
{
  perSystem =
    { system, ... }:
    let
      config.allowUnfree = true;
      pkgs = import inputs.nixpkgs {
        inherit system config;
      };
      coq = with pkgs; [
        coqPackages.coq
        coqPackages.coq-lsp
        dune_3
      ];
      python = import ./python.nix {
        inherit pkgs;
        coqpyt-src = inputs.coqpyt;
      };
      lean = [ pkgs.elan ];
      isabelle = [ pkgs.isabelle ];
      dafny = [ pkgs.dafny ];
      misc = with pkgs; [
        nodejs_24
        jq
        graphviz
        claude-code
      ];
      buildInputs = builtins.concatLists [
        coq
        python
        lean
        isabelle
        dafny
        misc
      ];
      name = "atomization";
      shellHook = "echo ${name}";
    in
    {
      devShells.default = pkgs.mkShell {
        inherit name buildInputs shellHook;
      };
    };
}
