SET_LD_LIBRARY_PATH = LD_LIBRARY_PATH="$$LD_LIBRARY_PATH:/home/fpoli/hg/jdk8u/build/linux-x86_64-normal-server-fastdebug/jdk/lib/amd64/server/"
#SET_LD_LIBRARY_PATH = LD_LIBRARY_PATH="$$LD_LIBRARY_PATH:$$JAVA_HOME/jre/lib/amd64/server/"
#SET_LD_LIBRARY_PATH = LD_LIBRARY_PATH="$$LD_LIBRARY_PATH:/usr/lib/jvm/java-8-openjdk-amd64/jre/lib/amd64/server/"
#SET_LD_LIBRARY_PATH = LD_LIBRARY_PATH="$$LD_LIBRARY_PATH:/usr/lib/jvm/java-8-oracle/jre/lib/amd64/server/"

default: build

fmt:
	cargo fmt || true

build: fmt
	cargo build

test: fmt
	$(SET_LD_LIBRARY_PATH) cargo test -- --nocapture

run:
	$(SET_LD_LIBRARY_PATH) cargo run

clean:
	cargo clean
	find . -name '*.bk' -delete
