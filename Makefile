RUST_LOG ?= viper=info,prusti_viper=info
RUST_BACKTRACE ?= 1
RUST_TEST_THREADS ?= 1
JAVA_HOME ?= /usr/lib/jvm/java-8-oracle
RUST_VERSION=nightly-2018-05-30-x86_64-unknown-linux-gnu
COMPILER_PATH=$$HOME/.rustup/toolchains/${RUST_VERSION}/
LD_LIBRARY_PATH = ${COMPILER_PATH}/lib/:${COMPILER_PATH}/lib/rustlib/x86_64-unknown-linux-gnu/lib/:./target/debug/:${JAVA_HOME}/jre/lib/amd64/server/

SET_ENV_VARS = RUST_LOG=$(RUST_LOG) RUST_BACKTRACE=$(RUST_BACKTRACE) LD_LIBRARY_PATH=$(LD_LIBRARY_PATH) JAVA_HOME=$(JAVA_HOME) RUST_TEST_THREADS=$(RUST_TEST_THREADS)

default: build

fmt:
	cargo fmt --all || true

check:
	$(SET_ENV_VARS) cargo check --all

build:
	$(SET_ENV_VARS) cargo build -vv --all

test:
	$(SET_ENV_VARS) cargo test --all

bench:
	$(SET_ENV_VARS) cargo bench --all

update:
	git submodule foreach git pull origin master
	cargo update

docs: update
	$(SET_ENV_VARS) cargo doc --all

clippy: clean
	$(SET_ENV_VARS) cargo clippy --all

clean:
	git submodule foreach cargo clean
	find . -name '*.bk' -delete

diff:
	git submodule foreach 'echo; echo "=== $$path ==="; git diff'

todo:
	git grep -i "todo\|fixme\|xxx\|hack"
