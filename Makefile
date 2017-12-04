SET_LD_LIBRARY_PATH = LD_LIBRARY_PATH="$$LD_LIBRARY_PATH:/home/fpoli/hg/jdk8u/build/linux-x86_64-normal-server-fastdebug/jdk/lib/amd64/server/"
#SET_LD_LIBRARY_PATH = LD_LIBRARY_PATH="$$LD_LIBRARY_PATH:$$JAVA_HOME/jre/lib/amd64/server/"
#SET_LD_LIBRARY_PATH = LD_LIBRARY_PATH="$$LD_LIBRARY_PATH:/usr/lib/jvm/java-8-openjdk-amd64/jre/lib/amd64/server/"
#SET_LD_LIBRARY_PATH = LD_LIBRARY_PATH="$$LD_LIBRARY_PATH:/usr/lib/jvm/java-8-oracle/jre/lib/amd64/server/"

default: build

build:
	cargo fmt ; cargo build

run:
	$(SET_LD_LIBRARY_PATH) RUST_BACKTRACE=1 cargo run

test:
	$(SET_LD_LIBRARY_PATH) RUST_BACKTRACE=1 cargo test -- --nocapture

clean:
	cargo clean
	find . -name '*.bk' -delete
