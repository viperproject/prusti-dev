Prusti-dev
==========

[![Build Status][build_badge]][build_status]

Workspace project containing all Prusti sub-projects.

[Development documentation][documentation]

[build_badge]: https://travis-ci.org/viperproject/prusti-dev.svg
[build_status]: https://travis-ci.org/viperproject/prusti-dev
[documentation]: https://viperproject.github.io/prusti-dev/


Get started
-----------

- Install the `viper` package.

    ```bash
    wget -q -O - http://pmserver.inf.ethz.ch/viper/debs/xenial/key.asc | sudo apt-key add -
    echo 'deb http://pmserver.inf.ethz.ch/viper/debs/xenial /' | sudo tee /etc/apt/sources.list.d/viper.list
    sudo apt-get install viper
    ```

- Install Java 8 or a later version.

    ```bash
    sudo apt-get install default-jre
    ```

- Check that the `JAVA_HOME` env var is set. If not, set it.

    ```bash
    export JAVA_HOME=/usr/lib/jvm/default-java
    ```

- Add `$JAVA_HOME/jre/lib/amd64/server/` to the `LD_LIBRARY_PATH` env var

    ```bash
    export LD_LIBRARY_PATH="$LD_LIBRARY_PATH:$JAVA_HOME/jre/lib/amd64/server/"
    ```

    Note: make sure that `LD_LIBRARY_PATH` does not contain empty
    segments because it can cause a crash with a “multiple inputs
    provided” error.

- Set the `ASM_JAR` env var to the location of the ASM Jar. If needed, download it.

    ```bash
    export ASM_JAR="/usr/share/java/asm4.jar"
    if [ ! -f "$ASM_JAR" ]; then
        export ASM_JAR="$HOME/asm.jar"
        wget "http://central.maven.org/maven2/asm/asm/3.3.1/asm-3.3.1.jar" -O "$ASM_JAR"
    fi
    ```

- You can now build all crates

    ```bash
    cargo build --all
    ```
