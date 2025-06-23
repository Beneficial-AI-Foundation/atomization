{
  description = "atomization";
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    parts.url = "github:hercules-ci/flake-parts";
    coqpyt = {
      url = "github:sr-lab/coqpyt";
      flake = false;
    };
    fmt.url = "github:numtide/treefmt-nix";
    pantograph.url = "github:lenianiva/Pantograph";
  };
  outputs =
    {
      self,
      nixpkgs,
      parts,
      coqpyt,
      fmt,
      pantograph,
    }@inputs:
    parts.lib.mkFlake { inherit inputs; } {
      systems = [
        "x86_64-linux"
        "aarch64-darwin"
        "aarch64-linux"
        "x86_64-darwin"
      ];
      imports = [
        ./nix/shell.nix
        fmt.flakeModule
        ./nix/fmt.nix
      ];
    };
}
