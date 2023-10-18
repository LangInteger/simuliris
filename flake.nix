{
  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
  };

  outputs = {
    self,
    flake-utils,
    nixpkgs,
  }:
  flake-utils.lib.eachDefaultSystem (system: let
    pkgs = import nixpkgs {inherit system;};
    inherit (pkgs) coqPackages;
  in rec {
    packages = {
      default = coqPackages.mkCoqDerivation {
        pname = "simuliris";
        version = "x.y.z";

        src = ./.;

        buildInputs = with coqPackages; [ equations iris ];
      };
    };

    devShells.default = pkgs.mkShell (with packages.default; {
      name = pname + "-dev";
      packages = buildInputs ++ [ pkgs.coq ];
    });
  });
}
