{
  pkgs,
  lib,
  config,
  inputs,
  ...
}:

{

  # https://devenv.sh/packages/
  packages = with pkgs; [
    wasm-pack
    lld
    llvm
    clang
  ];

  # https://devenv.sh/languages/
  languages.rust.enable = true;

  # https://devenv.sh/processes/
  # processes.dev.exec = "${lib.getExe pkgs.watchexec} -n -- ls -la";

  # https://devenv.sh/services/
  # services.postgres.enable = true;

  # https://devenv.sh/scripts/
  scripts.web-repl.exec = ''
    cd wasm/web
    wasm-pack build --target web || exit
    cd ../pkg
    npx serve . 
  '';

  scripts.bootstrap.exec = ''
    cargo run --release -- run lang/main.mo $@
  '';

  scripts.monad-rs.exec = ''
    cargo run --release -- $@
  '';

  # https://devenv.sh/basics/
  enterShell = "";

  # https://devenv.sh/tests/
  enterTest = "";

  # https://devenv.sh/git-hooks/
  git-hooks.hooks = {
    rustfmt.enable = true;
    clippy.enable = true;
    rust-tests = {
      enable = true;
      entry = ''
        cargo test --release
      '';
      pass_filenames = false;
      files = "\\.(rs|mo)$";
    };
    monad-tests = {
      enable = true;
      entry = ''
        cargo run --release -- test init std lang examples
      '';
      pass_filenames = false;
      files = "\\.(rs|mo)$";
    };
  };

  # See full reference at https://devenv.sh/reference/options/
}
