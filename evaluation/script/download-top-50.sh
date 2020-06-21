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

#  20 id=byteorder name=byteorder
mkdir -p "$CRATE_DOWNLOAD_DIR/020_byteorder"
wget -c "https://crates.io/api/v1/crates/byteorder/1.2.6/download" -O "$CRATE_DOWNLOAD_DIR/020_byteorder/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/020_byteorder/source"
tar -xf "$CRATE_DOWNLOAD_DIR/020_byteorder/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/020_byteorder/source" --strip-components=1

#  21 id=serde_json name=serde_json
mkdir -p "$CRATE_DOWNLOAD_DIR/021_serde_json"
wget -c "https://crates.io/api/v1/crates/serde_json/1.0.32/download" -O "$CRATE_DOWNLOAD_DIR/021_serde_json/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/021_serde_json/source"
tar -xf "$CRATE_DOWNLOAD_DIR/021_serde_json/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/021_serde_json/source" --strip-components=1

#  22 id=cfg-if name=cfg-if
mkdir -p "$CRATE_DOWNLOAD_DIR/022_cfg-if"
wget -c "https://crates.io/api/v1/crates/cfg-if/0.1.6/download" -O "$CRATE_DOWNLOAD_DIR/022_cfg-if/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/022_cfg-if/source"
tar -xf "$CRATE_DOWNLOAD_DIR/022_cfg-if/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/022_cfg-if/source" --strip-components=1

#  23 id=url name=url
mkdir -p "$CRATE_DOWNLOAD_DIR/023_url"
wget -c "https://crates.io/api/v1/crates/url/1.7.1/download" -O "$CRATE_DOWNLOAD_DIR/023_url/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/023_url/source"
tar -xf "$CRATE_DOWNLOAD_DIR/023_url/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/023_url/source" --strip-components=1

#  24 id=num_cpus name=num_cpus
mkdir -p "$CRATE_DOWNLOAD_DIR/024_num_cpus"
wget -c "https://crates.io/api/v1/crates/num_cpus/1.8.0/download" -O "$CRATE_DOWNLOAD_DIR/024_num_cpus/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/024_num_cpus/source"
tar -xf "$CRATE_DOWNLOAD_DIR/024_num_cpus/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/024_num_cpus/source" --strip-components=1

#  25 id=gcc name=gcc
mkdir -p "$CRATE_DOWNLOAD_DIR/025_gcc"
wget -c "https://crates.io/api/v1/crates/gcc/0.3.55/download" -O "$CRATE_DOWNLOAD_DIR/025_gcc/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/025_gcc/source"
tar -xf "$CRATE_DOWNLOAD_DIR/025_gcc/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/025_gcc/source" --strip-components=1

#  26 id=pkg-config name=pkg-config
mkdir -p "$CRATE_DOWNLOAD_DIR/026_pkg-config"
wget -c "https://crates.io/api/v1/crates/pkg-config/0.3.14/download" -O "$CRATE_DOWNLOAD_DIR/026_pkg-config/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/026_pkg-config/source"
tar -xf "$CRATE_DOWNLOAD_DIR/026_pkg-config/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/026_pkg-config/source" --strip-components=1

#  27 id=semver name=semver
mkdir -p "$CRATE_DOWNLOAD_DIR/027_semver"
wget -c "https://crates.io/api/v1/crates/semver/0.9.0/download" -O "$CRATE_DOWNLOAD_DIR/027_semver/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/027_semver/source"
tar -xf "$CRATE_DOWNLOAD_DIR/027_semver/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/027_semver/source" --strip-components=1

#  28 id=itoa name=itoa
mkdir -p "$CRATE_DOWNLOAD_DIR/028_itoa"
wget -c "https://crates.io/api/v1/crates/itoa/0.4.3/download" -O "$CRATE_DOWNLOAD_DIR/028_itoa/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/028_itoa/source"
tar -xf "$CRATE_DOWNLOAD_DIR/028_itoa/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/028_itoa/source" --strip-components=1

#  29 id=matches name=matches
mkdir -p "$CRATE_DOWNLOAD_DIR/029_matches"
wget -c "https://crates.io/api/v1/crates/matches/0.1.8/download" -O "$CRATE_DOWNLOAD_DIR/029_matches/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/029_matches/source"
tar -xf "$CRATE_DOWNLOAD_DIR/029_matches/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/029_matches/source" --strip-components=1

#  30 id=serde_derive name=serde_derive
mkdir -p "$CRATE_DOWNLOAD_DIR/030_serde_derive"
wget -c "https://crates.io/api/v1/crates/serde_derive/1.0.80/download" -O "$CRATE_DOWNLOAD_DIR/030_serde_derive/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/030_serde_derive/source"
tar -xf "$CRATE_DOWNLOAD_DIR/030_serde_derive/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/030_serde_derive/source" --strip-components=1

#  31 id=env_logger name=env_logger
mkdir -p "$CRATE_DOWNLOAD_DIR/031_env_logger"
wget -c "https://crates.io/api/v1/crates/env_logger/0.5.13/download" -O "$CRATE_DOWNLOAD_DIR/031_env_logger/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/031_env_logger/source"
tar -xf "$CRATE_DOWNLOAD_DIR/031_env_logger/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/031_env_logger/source" --strip-components=1

#  32 id=num-integer name=num-integer
mkdir -p "$CRATE_DOWNLOAD_DIR/032_num-integer"
wget -c "https://crates.io/api/v1/crates/num-integer/0.1.39/download" -O "$CRATE_DOWNLOAD_DIR/032_num-integer/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/032_num-integer/source"
tar -xf "$CRATE_DOWNLOAD_DIR/032_num-integer/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/032_num-integer/source" --strip-components=1

#  33 id=unicode-normalization name=unicode-normalization
mkdir -p "$CRATE_DOWNLOAD_DIR/033_unicode-normalization"
wget -c "https://crates.io/api/v1/crates/unicode-normalization/0.1.7/download" -O "$CRATE_DOWNLOAD_DIR/033_unicode-normalization/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/033_unicode-normalization/source"
tar -xf "$CRATE_DOWNLOAD_DIR/033_unicode-normalization/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/033_unicode-normalization/source" --strip-components=1

#  34 id=strsim name=strsim
mkdir -p "$CRATE_DOWNLOAD_DIR/034_strsim"
wget -c "https://crates.io/api/v1/crates/strsim/0.8.0/download" -O "$CRATE_DOWNLOAD_DIR/034_strsim/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/034_strsim/source"
tar -xf "$CRATE_DOWNLOAD_DIR/034_strsim/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/034_strsim/source" --strip-components=1

#  35 id=void name=void
mkdir -p "$CRATE_DOWNLOAD_DIR/035_void"
wget -c "https://crates.io/api/v1/crates/void/1.0.2/download" -O "$CRATE_DOWNLOAD_DIR/035_void/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/035_void/source"
tar -xf "$CRATE_DOWNLOAD_DIR/035_void/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/035_void/source" --strip-components=1

#  36 id=unicode-bidi name=unicode-bidi
mkdir -p "$CRATE_DOWNLOAD_DIR/036_unicode-bidi"
wget -c "https://crates.io/api/v1/crates/unicode-bidi/0.3.4/download" -O "$CRATE_DOWNLOAD_DIR/036_unicode-bidi/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/036_unicode-bidi/source"
tar -xf "$CRATE_DOWNLOAD_DIR/036_unicode-bidi/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/036_unicode-bidi/source" --strip-components=1

#  37 id=num name=num
mkdir -p "$CRATE_DOWNLOAD_DIR/037_num"
wget -c "https://crates.io/api/v1/crates/num/0.2.0/download" -O "$CRATE_DOWNLOAD_DIR/037_num/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/037_num/source"
tar -xf "$CRATE_DOWNLOAD_DIR/037_num/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/037_num/source" --strip-components=1

#  38 id=unreachable name=unreachable
mkdir -p "$CRATE_DOWNLOAD_DIR/038_unreachable"
wget -c "https://crates.io/api/v1/crates/unreachable/1.0.0/download" -O "$CRATE_DOWNLOAD_DIR/038_unreachable/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/038_unreachable/source"
tar -xf "$CRATE_DOWNLOAD_DIR/038_unreachable/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/038_unreachable/source" --strip-components=1

#  39 id=dtoa name=dtoa
mkdir -p "$CRATE_DOWNLOAD_DIR/039_dtoa"
wget -c "https://crates.io/api/v1/crates/dtoa/0.4.3/download" -O "$CRATE_DOWNLOAD_DIR/039_dtoa/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/039_dtoa/source"
tar -xf "$CRATE_DOWNLOAD_DIR/039_dtoa/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/039_dtoa/source" --strip-components=1

#  40 id=toml name=toml
mkdir -p "$CRATE_DOWNLOAD_DIR/040_toml"
wget -c "https://crates.io/api/v1/crates/toml/0.4.8/download" -O "$CRATE_DOWNLOAD_DIR/040_toml/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/040_toml/source"
tar -xf "$CRATE_DOWNLOAD_DIR/040_toml/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/040_toml/source" --strip-components=1

#  41 id=idna name=idna
mkdir -p "$CRATE_DOWNLOAD_DIR/041_idna"
wget -c "https://crates.io/api/v1/crates/idna/0.1.5/download" -O "$CRATE_DOWNLOAD_DIR/041_idna/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/041_idna/source"
tar -xf "$CRATE_DOWNLOAD_DIR/041_idna/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/041_idna/source" --strip-components=1

#  42 id=clap name=clap
mkdir -p "$CRATE_DOWNLOAD_DIR/042_clap"
wget -c "https://crates.io/api/v1/crates/clap/2.32.0/download" -O "$CRATE_DOWNLOAD_DIR/042_clap/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/042_clap/source"
tar -xf "$CRATE_DOWNLOAD_DIR/042_clap/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/042_clap/source" --strip-components=1

#  43 id=openssl-sys name=openssl-sys
mkdir -p "$CRATE_DOWNLOAD_DIR/043_openssl-sys"
wget -c "https://crates.io/api/v1/crates/openssl-sys/0.9.39/download" -O "$CRATE_DOWNLOAD_DIR/043_openssl-sys/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/043_openssl-sys/source"
tar -xf "$CRATE_DOWNLOAD_DIR/043_openssl-sys/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/043_openssl-sys/source" --strip-components=1

#  44 id=num-iter name=num-iter
mkdir -p "$CRATE_DOWNLOAD_DIR/044_num-iter"
wget -c "https://crates.io/api/v1/crates/num-iter/0.1.37/download" -O "$CRATE_DOWNLOAD_DIR/044_num-iter/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/044_num-iter/source"
tar -xf "$CRATE_DOWNLOAD_DIR/044_num-iter/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/044_num-iter/source" --strip-components=1

#  45 id=ansi_term name=ansi_term
mkdir -p "$CRATE_DOWNLOAD_DIR/045_ansi_term"
wget -c "https://crates.io/api/v1/crates/ansi_term/0.11.0/download" -O "$CRATE_DOWNLOAD_DIR/045_ansi_term/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/045_ansi_term/source"
tar -xf "$CRATE_DOWNLOAD_DIR/045_ansi_term/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/045_ansi_term/source" --strip-components=1

#  46 id=unicase name=unicase
mkdir -p "$CRATE_DOWNLOAD_DIR/046_unicase"
wget -c "https://crates.io/api/v1/crates/unicase/2.2.0/download" -O "$CRATE_DOWNLOAD_DIR/046_unicase/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/046_unicase/source"
tar -xf "$CRATE_DOWNLOAD_DIR/046_unicase/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/046_unicase/source" --strip-components=1

#  47 id=hyper name=hyper
mkdir -p "$CRATE_DOWNLOAD_DIR/047_hyper"
wget -c "https://crates.io/api/v1/crates/hyper/0.12.12/download" -O "$CRATE_DOWNLOAD_DIR/047_hyper/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/047_hyper/source"
tar -xf "$CRATE_DOWNLOAD_DIR/047_hyper/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/047_hyper/source" --strip-components=1

#  48 id=mime name=mime
mkdir -p "$CRATE_DOWNLOAD_DIR/048_mime"
wget -c "https://crates.io/api/v1/crates/mime/0.3.12/download" -O "$CRATE_DOWNLOAD_DIR/048_mime/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/048_mime/source"
tar -xf "$CRATE_DOWNLOAD_DIR/048_mime/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/048_mime/source" --strip-components=1

#  49 id=vec_map name=vec_map
mkdir -p "$CRATE_DOWNLOAD_DIR/049_vec_map"
wget -c "https://crates.io/api/v1/crates/vec_map/0.8.1/download" -O "$CRATE_DOWNLOAD_DIR/049_vec_map/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/049_vec_map/source"
tar -xf "$CRATE_DOWNLOAD_DIR/049_vec_map/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/049_vec_map/source" --strip-components=1
