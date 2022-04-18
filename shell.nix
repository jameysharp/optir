{ sources ? import nix/sources.nix }:

let
  pkgs = import sources.nixpkgs {
    overlays = [ (import sources.rust-overlay) ];
  };
in pkgs.mkShell {
  nativeBuildInputs = [
    pkgs.rust-bin.stable.latest.default
    pkgs.cargo-edit
    pkgs.z3.dev
  ];
  LIBCLANG_PATH = "${pkgs.libclang.lib}/lib";
}
