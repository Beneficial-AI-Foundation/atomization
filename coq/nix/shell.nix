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
      buildInputs = coq ++ python ++ [ pkgs.nodejs_23 pkgs.jq ];
      greeting = "Atomization with coq-lsp";
      shellHook = "echo ${greeting}";
      name = "coq-atomization";
    in
    {
      devShells.default = pkgs.mkShell {
        inherit name buildInputs shellHook;
      };
    };
}
