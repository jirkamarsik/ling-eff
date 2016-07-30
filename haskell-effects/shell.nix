with (import <nixpkgs-unstable> {}).pkgs;
let pkg = haskellngPackages.callPackage
            ({ mkDerivation, base, effect-handlers, extensible-effects, stdenv
             }:
             mkDerivation {
               pname = "linguistic-effects";
               version = "0.1.0.0";
               src = ./.;
               buildDepends = [ base effect-handlers extensible-effects ];
               homepage = "https://github.com/jirkamarsik/ling-eff";
               description = "Using effects and handlers for natural language semantics";
               license = stdenv.lib.licenses.mit;
             }) {};
in
  pkg.env
