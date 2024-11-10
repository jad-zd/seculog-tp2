{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };
  outputs =
    {
      self,
      nixpkgs,
    }:
    let
      pkgs = import nixpkgs {
        system = "x86_64-linux";
      };
    in
    {
      packages.x86_64-linux.default = pkgs.mkShell {
        buildInputs = with pkgs; [
          coq_8_12
          coqPackages.coqide
        ];

        shellHook = "exec $SHELL";
      };
    };
}
