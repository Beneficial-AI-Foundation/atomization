{ inputs, ... }:
{
  perSystem =
    { pkgs, ... }:
    let
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
      buildInputs =
        coq
        ++ python
        ++ lean
        ++ [
          pkgs.nodejs_23
          pkgs.jq
          pkgs.graphviz
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
