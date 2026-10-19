# Installation

## Prusti Assistant

The easiest way to try out Prusti is by using the ["Prusti Assistant"](https://marketplace.visualstudio.com/items?itemName=viper-admin.prusti-assistant) extension for [Visual Studio Code](https://code.visualstudio.com/). Please confer the extension's webpage for:
* Detailed installation and first usage instructions.
* The description of the available commands, among which are commands to run and update the verifier.
* The description of the configuration flags.
* Troubleshooting instructions.

> **Warning:** Some of the Prusti-specific syntax described in this guide is currently only available in the "LatestDev" version, which corresponds to the latest development build of Prusti.
> The setting for switching to this version in Prusti Assistant is found in
> `File → Preferences → Settings → Prusti Assistant → Prusti Version`.

In case you experience difficulties or encounter bugs while using Prusti Assistant, please [open an issue in Prusti Assistant's repository](https://github.com/prusti/prusti-assistant/issues) or contact us in the [Zulip chat](https://prusti.zulipchat.com/).
Bugs with Prusti itself can be reported on the [Prusti repository](https://github.com/prusti/prusti/issues).

## Command-line setup

Alternatively, Prusti can be set up by downloading the [precompiled binaries](https://github.com/prusti/prusti/releases) available from the project page. We currently provide binaries for Windows and macOS (both x64 and arm64), and Ubuntu. Releases marked as "Pre-release" may contain unstable or experimental features.

For a command-line setup with Prusti built from source, please confer the [developer guide](https://prusti.github.io/prusti/dev-guide/development/setup.html).
