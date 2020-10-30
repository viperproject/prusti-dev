# Installation

The easiest way to try out Prusti is by using the ["Prusti Assistant"](https://marketplace.visualstudio.com/items?itemName=viper-admin.prusti-assistant) extension for VS Code. When using the extension, ensure that:

- It is updated to the latest version. A restart might be required after an upgrade.
- The dependencies are up to date. To check this, open any Rust program, then open `View → Command Palette` and run `Prusti: update dependencies`.
- It uses the "nightly" Prusti version. The setting is found in `File → Preferences → Settings → Prusti Assistant → Build Channel`.

For a command-line setup with Prusti built from source, please see the [developer guide](https://viperproject.github.io/prusti-dev/dev-guide/development/setup.html).
