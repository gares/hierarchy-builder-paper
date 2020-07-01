#!/usr/bin/env nix-shell

# generated using /home/cyril/git/scripts/master/nix-mkshell "(with coqPackages_8_10; [ coq hierarchy-builder ]) ++ (with python3Packages; [pygments])"
{
  nixpkgs ? <nixpkgs>,
  print-env ? false,
  config ? {}
}:
with import nixpkgs config;
stdenv.mkDerivation {
  name = "env";
  buildInputs = (with coqPackages_8_11; [ coq hierarchy-builder ]) ++ (with python3Packages; [pygments]);
  shellHook = ''
    nixEnv () {
      echo "Here is your work environement"
      echo "buildInputs:"
      for x in $buildInputs; do printf "  "; echo $x | cut -d "-" -f "2-"; done
      echo "propagatedBuildInputs:"
      for x in $propagatedBuildInputs; do printf "  "; echo $x | cut -d "-" -f "2-"; done
      echo "you can pass option '--argstr coq-version \"x.y\"' to nix-shell to change coq versions"
      echo "you can pass option '--argstr mc-version \"x.y.z\"' to nix-shell to change mathcomp versions"
    }
    cachixEnv () {
      echo "Pushing environement to cachix"
      for x in $buildInputs; do printf "  "; echo $x | cachix push $1; done
      for x in $propagatedBuildInputs; do printf "  "; echo $x | cachix push $1; done
    }
  '';
}
