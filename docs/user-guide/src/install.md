# Installation

## Prusti Assistant

The easiest way to try out Prusti is by using the ["Prusti Assistant"](https://marketplace.visualstudio.com/items?itemName=viper-admin.prusti-assistant) extension for [Visual Studio Code](https://code.visualstudio.com/). Please confer the extension's webpage for detailed installation instructions.

To update the currently installed version of Prusti within Prusti Assistant, it suffices to open the [Command Palette](https://code.visualstudio.com/docs/getstarted/userinterface#_command-palette) and run the command `Prusti: update dependencies`.

> **Warning:** Some of the Prusti-specific syntax described in this guide is currently only available in the "nightly" build channel, which corresponds to the latest development version of Prusti.
> The settings for switching to this version in Prusti Assistant are found in
> `File → Preferences → Settings → Prusti Assistant → Build Channel`.

## Command-line setup

Alternatively, Prusti can be set up by downloading the [precompiled binaries](https://github.com/viperproject/prusti-dev/releases) available from the project page. We currently provide binaries for Windows, macOS, and Ubuntu. Releases marked as "Pre-release" may contain unstable or experimental features.

For a command-line setup with Prusti built from source, please confer the [developer guide](https://viperproject.github.io/prusti-dev/dev-guide/development/setup.html).
