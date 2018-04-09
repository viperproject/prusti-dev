RUST_LOG ?= viper=debug,viper-sys=debug,jni-gen=debug
RUST_BACKTRACE ?= 1
ASM_JAR ?= /usr/share/java/asm4.jar
LD_LIBRARY_PATH = "$$LD_LIBRARY_PATH:$$JAVA_HOME/jre/lib/amd64/server/"
#LD_LIBRARY_PATH = "$$LD_LIBRARY_PATH:/home/fpoli/hg/jdk8u/build/linux-x86_64-normal-server-fastdebug/jdk/lib/amd64/server/"
#LD_LIBRARY_PATH = "$$LD_LIBRARY_PATH:/usr/lib/jvm/java-8-openjdk-amd64/jre/lib/amd64/server/"
#LD_LIBRARY_PATH = "$$LD_LIBRARY_PATH:/usr/lib/jvm/java-8-oracle/jre/lib/amd64/server/"

SET_ENV_VARS = RUST_LOG=$(RUST_LOG) RUST_BACKTRACE=$(RUST_BACKTRACE) LD_LIBRARY_PATH=$(LD_LIBRARY_PATH) ASM_JAR=$(ASM_JAR)

default: build

fmt:
	cargo fmt || true

check:
	$(SET_ENV_VARS) cargo check

build:
	$(SET_ENV_VARS) cargo build -vv

test:
	$(SET_ENV_VARS) cargo test

test-local-viper:
	$(SET_ENV_VARS) VIPER_HOME=/home/fpoli/opt/viper cargo test -- --nocapture

test-local-viper-bug:
	$(SET_ENV_VARS) VIPER_HOME=/home/fpoli/opt/viper cargo test --test=concurrent_verifiers -- --nocapture

bench:
	$(SET_ENV_VARS) cargo bench

update:
	cargo update

docs: update
	$(SET_ENV_VARS) cargo doc

clippy:
	$(SET_ENV_VARS) cargo clippy

clean:
	cargo clean
	find . -name '*.bk' -delete

todo:
	git grep -i "todo\|fixme\|xxx\|hack"
