{ ... }:
{
  perSystem =
    { ... }:
    {
      treefmt.config = {
        projectRootFile = "flake.nix";
        programs = {
          nixfmt.enable = true;
          prettier.enable = true;
          ruff-format.enable = true;
        };
      };
    };
}
