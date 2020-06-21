#!/bin/bash

if [[ ! -d "$1" ]]; then
	echo "It looks like CRATE_DOWNLOAD_DIR (the first argument) does not exist: '$1'"
	exit 1
fi

# Get the folder in which to download all the crates
CRATE_DOWNLOAD_DIR="$(cd "${1:-.}" && pwd)"

if [[ ! -z "$(ls -A "$CRATE_DOWNLOAD_DIR")" ]]; then
	echo "It looks like CRATE_DOWNLOAD_DIR (the first argument) is not empty: '$CRATE_DOWNLOAD_DIR'"
	exit 1
fi

#   0 id=libc name=libc
mkdir -p "$CRATE_DOWNLOAD_DIR/000_libc"
wget -c "https://crates.io/api/v1/crates/libc/0.2.43/download" -O "$CRATE_DOWNLOAD_DIR/000_libc/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/000_libc/source"
tar -xf "$CRATE_DOWNLOAD_DIR/000_libc/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/000_libc/source" --strip-components=1

#   1 id=bitflags name=bitflags
mkdir -p "$CRATE_DOWNLOAD_DIR/001_bitflags"
wget -c "https://crates.io/api/v1/crates/bitflags/1.0.4/download" -O "$CRATE_DOWNLOAD_DIR/001_bitflags/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/001_bitflags/source"
tar -xf "$CRATE_DOWNLOAD_DIR/001_bitflags/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/001_bitflags/source" --strip-components=1

#   2 id=log name=log
mkdir -p "$CRATE_DOWNLOAD_DIR/002_log"
wget -c "https://crates.io/api/v1/crates/log/0.4.5/download" -O "$CRATE_DOWNLOAD_DIR/002_log/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/002_log/source"
tar -xf "$CRATE_DOWNLOAD_DIR/002_log/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/002_log/source" --strip-components=1

#   3 id=lazy_static name=lazy_static
mkdir -p "$CRATE_DOWNLOAD_DIR/003_lazy_static"
wget -c "https://crates.io/api/v1/crates/lazy_static/1.1.0/download" -O "$CRATE_DOWNLOAD_DIR/003_lazy_static/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/003_lazy_static/source"
tar -xf "$CRATE_DOWNLOAD_DIR/003_lazy_static/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/003_lazy_static/source" --strip-components=1

#   4 id=serde name=serde
mkdir -p "$CRATE_DOWNLOAD_DIR/004_serde"
wget -c "https://crates.io/api/v1/crates/serde/1.0.80/download" -O "$CRATE_DOWNLOAD_DIR/004_serde/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/004_serde/source"
tar -xf "$CRATE_DOWNLOAD_DIR/004_serde/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/004_serde/source" --strip-components=1

#   5 id=winapi name=winapi
mkdir -p "$CRATE_DOWNLOAD_DIR/005_winapi"
wget -c "https://crates.io/api/v1/crates/winapi/0.3.6/download" -O "$CRATE_DOWNLOAD_DIR/005_winapi/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/005_winapi/source"
tar -xf "$CRATE_DOWNLOAD_DIR/005_winapi/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/005_winapi/source" --strip-components=1

#   6 id=regex name=regex
mkdir -p "$CRATE_DOWNLOAD_DIR/006_regex"
wget -c "https://crates.io/api/v1/crates/regex/1.0.5/download" -O "$CRATE_DOWNLOAD_DIR/006_regex/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/006_regex/source"
tar -xf "$CRATE_DOWNLOAD_DIR/006_regex/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/006_regex/source" --strip-components=1

#   7 id=regex-syntax name=regex-syntax
mkdir -p "$CRATE_DOWNLOAD_DIR/007_regex-syntax"
wget -c "https://crates.io/api/v1/crates/regex-syntax/0.6.2/download" -O "$CRATE_DOWNLOAD_DIR/007_regex-syntax/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/007_regex-syntax/source"
tar -xf "$CRATE_DOWNLOAD_DIR/007_regex-syntax/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/007_regex-syntax/source" --strip-components=1

#   8 id=num-traits name=num-traits
mkdir -p "$CRATE_DOWNLOAD_DIR/008_num-traits"
wget -c "https://crates.io/api/v1/crates/num-traits/0.2.6/download" -O "$CRATE_DOWNLOAD_DIR/008_num-traits/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/008_num-traits/source"
tar -xf "$CRATE_DOWNLOAD_DIR/008_num-traits/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/008_num-traits/source" --strip-components=1

#   9 id=memchr name=memchr
mkdir -p "$CRATE_DOWNLOAD_DIR/009_memchr"
wget -c "https://crates.io/api/v1/crates/memchr/2.1.0/download" -O "$CRATE_DOWNLOAD_DIR/009_memchr/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/009_memchr/source"
tar -xf "$CRATE_DOWNLOAD_DIR/009_memchr/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/009_memchr/source" --strip-components=1

#  10 id=rustc-serialize name=rustc-serialize
mkdir -p "$CRATE_DOWNLOAD_DIR/010_rustc-serialize"
wget -c "https://crates.io/api/v1/crates/rustc-serialize/0.3.24/download" -O "$CRATE_DOWNLOAD_DIR/010_rustc-serialize/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/010_rustc-serialize/source"
tar -xf "$CRATE_DOWNLOAD_DIR/010_rustc-serialize/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/010_rustc-serialize/source" --strip-components=1

#  11 id=syn name=syn
mkdir -p "$CRATE_DOWNLOAD_DIR/011_syn"
wget -c "https://crates.io/api/v1/crates/syn/0.15.13/download" -O "$CRATE_DOWNLOAD_DIR/011_syn/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/011_syn/source"
tar -xf "$CRATE_DOWNLOAD_DIR/011_syn/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/011_syn/source" --strip-components=1

#  12 id=unicode-xid name=unicode-xid
mkdir -p "$CRATE_DOWNLOAD_DIR/012_unicode-xid"
wget -c "https://crates.io/api/v1/crates/unicode-xid/0.1.0/download" -O "$CRATE_DOWNLOAD_DIR/012_unicode-xid/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/012_unicode-xid/source"
tar -xf "$CRATE_DOWNLOAD_DIR/012_unicode-xid/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/012_unicode-xid/source" --strip-components=1

#  13 id=aho-corasick name=aho-corasick
mkdir -p "$CRATE_DOWNLOAD_DIR/013_aho-corasick"
wget -c "https://crates.io/api/v1/crates/aho-corasick/0.6.8/download" -O "$CRATE_DOWNLOAD_DIR/013_aho-corasick/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/013_aho-corasick/source"
tar -xf "$CRATE_DOWNLOAD_DIR/013_aho-corasick/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/013_aho-corasick/source" --strip-components=1

#  14 id=winapi-build name=winapi-build
mkdir -p "$CRATE_DOWNLOAD_DIR/014_winapi-build"
wget -c "https://crates.io/api/v1/crates/winapi-build/0.1.1/download" -O "$CRATE_DOWNLOAD_DIR/014_winapi-build/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/014_winapi-build/source"
tar -xf "$CRATE_DOWNLOAD_DIR/014_winapi-build/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/014_winapi-build/source" --strip-components=1

#  15 id=quote name=quote
mkdir -p "$CRATE_DOWNLOAD_DIR/015_quote"
wget -c "https://crates.io/api/v1/crates/quote/0.6.8/download" -O "$CRATE_DOWNLOAD_DIR/015_quote/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/015_quote/source"
tar -xf "$CRATE_DOWNLOAD_DIR/015_quote/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/015_quote/source" --strip-components=1

#  16 id=kernel32-sys name=kernel32-sys
mkdir -p "$CRATE_DOWNLOAD_DIR/016_kernel32-sys"
wget -c "https://crates.io/api/v1/crates/kernel32-sys/0.2.2/download" -O "$CRATE_DOWNLOAD_DIR/016_kernel32-sys/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/016_kernel32-sys/source"
tar -xf "$CRATE_DOWNLOAD_DIR/016_kernel32-sys/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/016_kernel32-sys/source" --strip-components=1

#  17 id=thread_local name=thread_local
mkdir -p "$CRATE_DOWNLOAD_DIR/017_thread_local"
wget -c "https://crates.io/api/v1/crates/thread_local/0.3.6/download" -O "$CRATE_DOWNLOAD_DIR/017_thread_local/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/017_thread_local/source"
tar -xf "$CRATE_DOWNLOAD_DIR/017_thread_local/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/017_thread_local/source" --strip-components=1

#  18 id=time name=time
mkdir -p "$CRATE_DOWNLOAD_DIR/018_time"
wget -c "https://crates.io/api/v1/crates/time/0.1.40/download" -O "$CRATE_DOWNLOAD_DIR/018_time/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/018_time/source"
tar -xf "$CRATE_DOWNLOAD_DIR/018_time/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/018_time/source" --strip-components=1

#  19 id=utf8-ranges name=utf8-ranges
mkdir -p "$CRATE_DOWNLOAD_DIR/019_utf8-ranges"
wget -c "https://crates.io/api/v1/crates/utf8-ranges/1.0.1/download" -O "$CRATE_DOWNLOAD_DIR/019_utf8-ranges/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/019_utf8-ranges/source"
tar -xf "$CRATE_DOWNLOAD_DIR/019_utf8-ranges/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/019_utf8-ranges/source" --strip-components=1
