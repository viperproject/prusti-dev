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

#  50 id=chrono name=chrono
mkdir -p "$CRATE_DOWNLOAD_DIR/050_chrono"
wget -c "https://crates.io/api/v1/crates/chrono/0.4.6/download" -O "$CRATE_DOWNLOAD_DIR/050_chrono/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/050_chrono/source"
tar -xf "$CRATE_DOWNLOAD_DIR/050_chrono/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/050_chrono/source" --strip-components=1

#  51 id=unicode-width name=unicode-width
mkdir -p "$CRATE_DOWNLOAD_DIR/051_unicode-width"
wget -c "https://crates.io/api/v1/crates/unicode-width/0.1.5/download" -O "$CRATE_DOWNLOAD_DIR/051_unicode-width/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/051_unicode-width/source"
tar -xf "$CRATE_DOWNLOAD_DIR/051_unicode-width/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/051_unicode-width/source" --strip-components=1

#  52 id=slab name=slab
mkdir -p "$CRATE_DOWNLOAD_DIR/052_slab"
wget -c "https://crates.io/api/v1/crates/slab/0.4.1/download" -O "$CRATE_DOWNLOAD_DIR/052_slab/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/052_slab/source"
tar -xf "$CRATE_DOWNLOAD_DIR/052_slab/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/052_slab/source" --strip-components=1

#  53 id=cc name=cc
mkdir -p "$CRATE_DOWNLOAD_DIR/053_cc"
wget -c "https://crates.io/api/v1/crates/cc/1.0.25/download" -O "$CRATE_DOWNLOAD_DIR/053_cc/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/053_cc/source"
tar -xf "$CRATE_DOWNLOAD_DIR/053_cc/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/053_cc/source" --strip-components=1

#  54 id=term name=term
mkdir -p "$CRATE_DOWNLOAD_DIR/054_term"
wget -c "https://crates.io/api/v1/crates/term/0.5.1/download" -O "$CRATE_DOWNLOAD_DIR/054_term/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/054_term/source"
tar -xf "$CRATE_DOWNLOAD_DIR/054_term/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/054_term/source" --strip-components=1

#  55 id=thread-id name=thread-id
mkdir -p "$CRATE_DOWNLOAD_DIR/055_thread-id"
wget -c "https://crates.io/api/v1/crates/thread-id/3.3.0/download" -O "$CRATE_DOWNLOAD_DIR/055_thread-id/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/055_thread-id/source"
tar -xf "$CRATE_DOWNLOAD_DIR/055_thread-id/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/055_thread-id/source" --strip-components=1

#  56 id=atty name=atty
mkdir -p "$CRATE_DOWNLOAD_DIR/056_atty"
wget -c "https://crates.io/api/v1/crates/atty/0.2.11/download" -O "$CRATE_DOWNLOAD_DIR/056_atty/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/056_atty/source"
tar -xf "$CRATE_DOWNLOAD_DIR/056_atty/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/056_atty/source" --strip-components=1

#  57 id=openssl name=openssl
mkdir -p "$CRATE_DOWNLOAD_DIR/057_openssl"
wget -c "https://crates.io/api/v1/crates/openssl/0.10.15/download" -O "$CRATE_DOWNLOAD_DIR/057_openssl/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/057_openssl/source"
tar -xf "$CRATE_DOWNLOAD_DIR/057_openssl/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/057_openssl/source" --strip-components=1

#  58 id=backtrace name=backtrace
mkdir -p "$CRATE_DOWNLOAD_DIR/058_backtrace"
wget -c "https://crates.io/api/v1/crates/backtrace/0.3.9/download" -O "$CRATE_DOWNLOAD_DIR/058_backtrace/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/058_backtrace/source"
tar -xf "$CRATE_DOWNLOAD_DIR/058_backtrace/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/058_backtrace/source" --strip-components=1

#  59 id=tempdir name=tempdir
mkdir -p "$CRATE_DOWNLOAD_DIR/059_tempdir"
wget -c "https://crates.io/api/v1/crates/tempdir/0.3.7/download" -O "$CRATE_DOWNLOAD_DIR/059_tempdir/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/059_tempdir/source"
tar -xf "$CRATE_DOWNLOAD_DIR/059_tempdir/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/059_tempdir/source" --strip-components=1

#  60 id=httparse name=httparse
mkdir -p "$CRATE_DOWNLOAD_DIR/060_httparse"
wget -c "https://crates.io/api/v1/crates/httparse/1.3.3/download" -O "$CRATE_DOWNLOAD_DIR/060_httparse/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/060_httparse/source"
tar -xf "$CRATE_DOWNLOAD_DIR/060_httparse/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/060_httparse/source" --strip-components=1

#  61 id=rustc_version name=rustc_version
mkdir -p "$CRATE_DOWNLOAD_DIR/061_rustc_version"
wget -c "https://crates.io/api/v1/crates/rustc_version/0.2.3/download" -O "$CRATE_DOWNLOAD_DIR/061_rustc_version/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/061_rustc_version/source"
tar -xf "$CRATE_DOWNLOAD_DIR/061_rustc_version/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/061_rustc_version/source" --strip-components=1

#  62 id=error-chain name=error-chain
mkdir -p "$CRATE_DOWNLOAD_DIR/062_error-chain"
wget -c "https://crates.io/api/v1/crates/error-chain/0.12.0/download" -O "$CRATE_DOWNLOAD_DIR/062_error-chain/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/062_error-chain/source"
tar -xf "$CRATE_DOWNLOAD_DIR/062_error-chain/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/062_error-chain/source" --strip-components=1

#  63 id=smallvec name=smallvec
mkdir -p "$CRATE_DOWNLOAD_DIR/063_smallvec"
wget -c "https://crates.io/api/v1/crates/smallvec/0.6.5/download" -O "$CRATE_DOWNLOAD_DIR/063_smallvec/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/063_smallvec/source"
tar -xf "$CRATE_DOWNLOAD_DIR/063_smallvec/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/063_smallvec/source" --strip-components=1

#  64 id=synom name=synom
mkdir -p "$CRATE_DOWNLOAD_DIR/064_synom"
wget -c "https://crates.io/api/v1/crates/synom/0.11.3/download" -O "$CRATE_DOWNLOAD_DIR/064_synom/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/064_synom/source"
tar -xf "$CRATE_DOWNLOAD_DIR/064_synom/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/064_synom/source" --strip-components=1

#  65 id=rustc-demangle name=rustc-demangle
mkdir -p "$CRATE_DOWNLOAD_DIR/065_rustc-demangle"
wget -c "https://crates.io/api/v1/crates/rustc-demangle/0.1.9/download" -O "$CRATE_DOWNLOAD_DIR/065_rustc-demangle/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/065_rustc-demangle/source"
tar -xf "$CRATE_DOWNLOAD_DIR/065_rustc-demangle/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/065_rustc-demangle/source" --strip-components=1

#  66 id=proc-macro2 name=proc-macro2
mkdir -p "$CRATE_DOWNLOAD_DIR/066_proc-macro2"
wget -c "https://crates.io/api/v1/crates/proc-macro2/0.4.20/download" -O "$CRATE_DOWNLOAD_DIR/066_proc-macro2/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/066_proc-macro2/source"
tar -xf "$CRATE_DOWNLOAD_DIR/066_proc-macro2/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/066_proc-macro2/source" --strip-components=1

#  67 id=base64 name=base64
mkdir -p "$CRATE_DOWNLOAD_DIR/067_base64"
wget -c "https://crates.io/api/v1/crates/base64/0.9.3/download" -O "$CRATE_DOWNLOAD_DIR/067_base64/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/067_base64/source"
tar -xf "$CRATE_DOWNLOAD_DIR/067_base64/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/067_base64/source" --strip-components=1

#  68 id=uuid name=uuid
mkdir -p "$CRATE_DOWNLOAD_DIR/068_uuid"
wget -c "https://crates.io/api/v1/crates/uuid/0.7.1/download" -O "$CRATE_DOWNLOAD_DIR/068_uuid/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/068_uuid/source"
tar -xf "$CRATE_DOWNLOAD_DIR/068_uuid/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/068_uuid/source" --strip-components=1

#  69 id=net2 name=net2
mkdir -p "$CRATE_DOWNLOAD_DIR/069_net2"
wget -c "https://crates.io/api/v1/crates/net2/0.2.33/download" -O "$CRATE_DOWNLOAD_DIR/069_net2/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/069_net2/source"
tar -xf "$CRATE_DOWNLOAD_DIR/069_net2/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/069_net2/source" --strip-components=1

#  70 id=language-tags name=language-tags
mkdir -p "$CRATE_DOWNLOAD_DIR/070_language-tags"
wget -c "https://crates.io/api/v1/crates/language-tags/0.2.2/download" -O "$CRATE_DOWNLOAD_DIR/070_language-tags/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/070_language-tags/source"
tar -xf "$CRATE_DOWNLOAD_DIR/070_language-tags/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/070_language-tags/source" --strip-components=1

#  71 id=percent-encoding name=percent-encoding
mkdir -p "$CRATE_DOWNLOAD_DIR/071_percent-encoding"
wget -c "https://crates.io/api/v1/crates/percent-encoding/1.0.1/download" -O "$CRATE_DOWNLOAD_DIR/071_percent-encoding/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/071_percent-encoding/source"
tar -xf "$CRATE_DOWNLOAD_DIR/071_percent-encoding/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/071_percent-encoding/source" --strip-components=1

#  72 id=traitobject name=traitobject
mkdir -p "$CRATE_DOWNLOAD_DIR/072_traitobject"
wget -c "https://crates.io/api/v1/crates/traitobject/0.1.0/download" -O "$CRATE_DOWNLOAD_DIR/072_traitobject/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/072_traitobject/source"
tar -xf "$CRATE_DOWNLOAD_DIR/072_traitobject/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/072_traitobject/source" --strip-components=1

#  73 id=backtrace-sys name=backtrace-sys
mkdir -p "$CRATE_DOWNLOAD_DIR/073_backtrace-sys"
wget -c "https://crates.io/api/v1/crates/backtrace-sys/0.1.24/download" -O "$CRATE_DOWNLOAD_DIR/073_backtrace-sys/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/073_backtrace-sys/source"
tar -xf "$CRATE_DOWNLOAD_DIR/073_backtrace-sys/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/073_backtrace-sys/source" --strip-components=1

#  74 id=futures name=futures
mkdir -p "$CRATE_DOWNLOAD_DIR/074_futures"
wget -c "https://crates.io/api/v1/crates/futures/0.1.25/download" -O "$CRATE_DOWNLOAD_DIR/074_futures/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/074_futures/source"
tar -xf "$CRATE_DOWNLOAD_DIR/074_futures/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/074_futures/source" --strip-components=1

#  75 id=lazycell name=lazycell
mkdir -p "$CRATE_DOWNLOAD_DIR/075_lazycell"
wget -c "https://crates.io/api/v1/crates/lazycell/1.2.0/download" -O "$CRATE_DOWNLOAD_DIR/075_lazycell/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/075_lazycell/source"
tar -xf "$CRATE_DOWNLOAD_DIR/075_lazycell/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/075_lazycell/source" --strip-components=1

#  76 id=serde_derive_internals name=serde_derive_internals
mkdir -p "$CRATE_DOWNLOAD_DIR/076_serde_derive_internals"
wget -c "https://crates.io/api/v1/crates/serde_derive_internals/0.23.1/download" -O "$CRATE_DOWNLOAD_DIR/076_serde_derive_internals/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/076_serde_derive_internals/source"
tar -xf "$CRATE_DOWNLOAD_DIR/076_serde_derive_internals/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/076_serde_derive_internals/source" --strip-components=1

#  77 id=quick-error name=quick-error
mkdir -p "$CRATE_DOWNLOAD_DIR/077_quick-error"
wget -c "https://crates.io/api/v1/crates/quick-error/1.2.2/download" -O "$CRATE_DOWNLOAD_DIR/077_quick-error/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/077_quick-error/source"
tar -xf "$CRATE_DOWNLOAD_DIR/077_quick-error/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/077_quick-error/source" --strip-components=1

#  78 id=crossbeam name=crossbeam
mkdir -p "$CRATE_DOWNLOAD_DIR/078_crossbeam"
wget -c "https://crates.io/api/v1/crates/crossbeam/0.4.1/download" -O "$CRATE_DOWNLOAD_DIR/078_crossbeam/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/078_crossbeam/source"
tar -xf "$CRATE_DOWNLOAD_DIR/078_crossbeam/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/078_crossbeam/source" --strip-components=1

#  79 id=flate2 name=flate2
mkdir -p "$CRATE_DOWNLOAD_DIR/079_flate2"
wget -c "https://crates.io/api/v1/crates/flate2/1.0.4/download" -O "$CRATE_DOWNLOAD_DIR/079_flate2/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/079_flate2/source"
tar -xf "$CRATE_DOWNLOAD_DIR/079_flate2/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/079_flate2/source" --strip-components=1

#  80 id=itertools name=itertools
mkdir -p "$CRATE_DOWNLOAD_DIR/080_itertools"
wget -c "https://crates.io/api/v1/crates/itertools/0.7.8/download" -O "$CRATE_DOWNLOAD_DIR/080_itertools/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/080_itertools/source"
tar -xf "$CRATE_DOWNLOAD_DIR/080_itertools/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/080_itertools/source" --strip-components=1

#  81 id=mio name=mio
mkdir -p "$CRATE_DOWNLOAD_DIR/081_mio"
wget -c "https://crates.io/api/v1/crates/mio/0.6.16/download" -O "$CRATE_DOWNLOAD_DIR/081_mio/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/081_mio/source"
tar -xf "$CRATE_DOWNLOAD_DIR/081_mio/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/081_mio/source" --strip-components=1

#  82 id=textwrap name=textwrap
mkdir -p "$CRATE_DOWNLOAD_DIR/082_textwrap"
wget -c "https://crates.io/api/v1/crates/textwrap/0.10.0/download" -O "$CRATE_DOWNLOAD_DIR/082_textwrap/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/082_textwrap/source"
tar -xf "$CRATE_DOWNLOAD_DIR/082_textwrap/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/082_textwrap/source" --strip-components=1

#  83 id=scopeguard name=scopeguard
mkdir -p "$CRATE_DOWNLOAD_DIR/083_scopeguard"
wget -c "https://crates.io/api/v1/crates/scopeguard/0.3.3/download" -O "$CRATE_DOWNLOAD_DIR/083_scopeguard/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/083_scopeguard/source"
tar -xf "$CRATE_DOWNLOAD_DIR/083_scopeguard/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/083_scopeguard/source" --strip-components=1

#  84 id=bytes name=bytes
mkdir -p "$CRATE_DOWNLOAD_DIR/084_bytes"
wget -c "https://crates.io/api/v1/crates/bytes/0.4.10/download" -O "$CRATE_DOWNLOAD_DIR/084_bytes/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/084_bytes/source"
tar -xf "$CRATE_DOWNLOAD_DIR/084_bytes/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/084_bytes/source" --strip-components=1

#  85 id=syntex_syntax name=syntex_syntax
mkdir -p "$CRATE_DOWNLOAD_DIR/085_syntex_syntax"
wget -c "https://crates.io/api/v1/crates/syntex_syntax/0.59.1/download" -O "$CRATE_DOWNLOAD_DIR/085_syntex_syntax/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/085_syntex_syntax/source"
tar -xf "$CRATE_DOWNLOAD_DIR/085_syntex_syntax/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/085_syntex_syntax/source" --strip-components=1

#  86 id=getopts name=getopts
mkdir -p "$CRATE_DOWNLOAD_DIR/086_getopts"
wget -c "https://crates.io/api/v1/crates/getopts/0.2.18/download" -O "$CRATE_DOWNLOAD_DIR/086_getopts/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/086_getopts/source"
tar -xf "$CRATE_DOWNLOAD_DIR/086_getopts/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/086_getopts/source" --strip-components=1

#  87 id=nodrop name=nodrop
mkdir -p "$CRATE_DOWNLOAD_DIR/087_nodrop"
wget -c "https://crates.io/api/v1/crates/nodrop/0.1.12/download" -O "$CRATE_DOWNLOAD_DIR/087_nodrop/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/087_nodrop/source"
tar -xf "$CRATE_DOWNLOAD_DIR/087_nodrop/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/087_nodrop/source" --strip-components=1

#  88 id=glob name=glob
mkdir -p "$CRATE_DOWNLOAD_DIR/088_glob"
wget -c "https://crates.io/api/v1/crates/glob/0.2.11/download" -O "$CRATE_DOWNLOAD_DIR/088_glob/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/088_glob/source"
tar -xf "$CRATE_DOWNLOAD_DIR/088_glob/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/088_glob/source" --strip-components=1

#  89 id=either name=either
mkdir -p "$CRATE_DOWNLOAD_DIR/089_either"
wget -c "https://crates.io/api/v1/crates/either/1.5.0/download" -O "$CRATE_DOWNLOAD_DIR/089_either/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/089_either/source"
tar -xf "$CRATE_DOWNLOAD_DIR/089_either/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/089_either/source" --strip-components=1

#  90 id=typeable name=typeable
mkdir -p "$CRATE_DOWNLOAD_DIR/090_typeable"
wget -c "https://crates.io/api/v1/crates/typeable/0.1.2/download" -O "$CRATE_DOWNLOAD_DIR/090_typeable/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/090_typeable/source"
tar -xf "$CRATE_DOWNLOAD_DIR/090_typeable/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/090_typeable/source" --strip-components=1

#  91 id=miniz-sys name=miniz-sys
mkdir -p "$CRATE_DOWNLOAD_DIR/091_miniz-sys"
wget -c "https://crates.io/api/v1/crates/miniz-sys/0.1.11/download" -O "$CRATE_DOWNLOAD_DIR/091_miniz-sys/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/091_miniz-sys/source"
tar -xf "$CRATE_DOWNLOAD_DIR/091_miniz-sys/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/091_miniz-sys/source" --strip-components=1

#  92 id=walkdir name=walkdir
mkdir -p "$CRATE_DOWNLOAD_DIR/092_walkdir"
wget -c "https://crates.io/api/v1/crates/walkdir/2.2.5/download" -O "$CRATE_DOWNLOAD_DIR/092_walkdir/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/092_walkdir/source"
tar -xf "$CRATE_DOWNLOAD_DIR/092_walkdir/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/092_walkdir/source" --strip-components=1

#  93 id=unicode-segmentation name=unicode-segmentation
mkdir -p "$CRATE_DOWNLOAD_DIR/093_unicode-segmentation"
wget -c "https://crates.io/api/v1/crates/unicode-segmentation/1.2.1/download" -O "$CRATE_DOWNLOAD_DIR/093_unicode-segmentation/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/093_unicode-segmentation/source"
tar -xf "$CRATE_DOWNLOAD_DIR/093_unicode-segmentation/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/093_unicode-segmentation/source" --strip-components=1

#  94 id=fnv name=fnv
mkdir -p "$CRATE_DOWNLOAD_DIR/094_fnv"
wget -c "https://crates.io/api/v1/crates/fnv/1.0.6/download" -O "$CRATE_DOWNLOAD_DIR/094_fnv/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/094_fnv/source"
tar -xf "$CRATE_DOWNLOAD_DIR/094_fnv/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/094_fnv/source" --strip-components=1

#  95 id=num-rational name=num-rational
mkdir -p "$CRATE_DOWNLOAD_DIR/095_num-rational"
wget -c "https://crates.io/api/v1/crates/num-rational/0.2.1/download" -O "$CRATE_DOWNLOAD_DIR/095_num-rational/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/095_num-rational/source"
tar -xf "$CRATE_DOWNLOAD_DIR/095_num-rational/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/095_num-rational/source" --strip-components=1

#  96 id=libz-sys name=libz-sys
mkdir -p "$CRATE_DOWNLOAD_DIR/096_libz-sys"
wget -c "https://crates.io/api/v1/crates/libz-sys/1.0.24/download" -O "$CRATE_DOWNLOAD_DIR/096_libz-sys/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/096_libz-sys/source"
tar -xf "$CRATE_DOWNLOAD_DIR/096_libz-sys/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/096_libz-sys/source" --strip-components=1

#  97 id=version_check name=version_check
mkdir -p "$CRATE_DOWNLOAD_DIR/097_version_check"
wget -c "https://crates.io/api/v1/crates/version_check/0.1.5/download" -O "$CRATE_DOWNLOAD_DIR/097_version_check/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/097_version_check/source"
tar -xf "$CRATE_DOWNLOAD_DIR/097_version_check/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/097_version_check/source" --strip-components=1

#  98 id=crossbeam-utils name=crossbeam-utils
mkdir -p "$CRATE_DOWNLOAD_DIR/098_crossbeam-utils"
wget -c "https://crates.io/api/v1/crates/crossbeam-utils/0.5.0/download" -O "$CRATE_DOWNLOAD_DIR/098_crossbeam-utils/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/098_crossbeam-utils/source"
tar -xf "$CRATE_DOWNLOAD_DIR/098_crossbeam-utils/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/098_crossbeam-utils/source" --strip-components=1

#  99 id=semver-parser name=semver-parser
mkdir -p "$CRATE_DOWNLOAD_DIR/099_semver-parser"
wget -c "https://crates.io/api/v1/crates/semver-parser/0.9.0/download" -O "$CRATE_DOWNLOAD_DIR/099_semver-parser/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/099_semver-parser/source"
tar -xf "$CRATE_DOWNLOAD_DIR/099_semver-parser/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/099_semver-parser/source" --strip-components=1

# 100 id=rayon name=rayon
mkdir -p "$CRATE_DOWNLOAD_DIR/100_rayon"
wget -c "https://crates.io/api/v1/crates/rayon/1.0.2/download" -O "$CRATE_DOWNLOAD_DIR/100_rayon/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/100_rayon/source"
tar -xf "$CRATE_DOWNLOAD_DIR/100_rayon/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/100_rayon/source" --strip-components=1

# 101 id=arrayvec name=arrayvec
mkdir -p "$CRATE_DOWNLOAD_DIR/101_arrayvec"
wget -c "https://crates.io/api/v1/crates/arrayvec/0.4.7/download" -O "$CRATE_DOWNLOAD_DIR/101_arrayvec/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/101_arrayvec/source"
tar -xf "$CRATE_DOWNLOAD_DIR/101_arrayvec/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/101_arrayvec/source" --strip-components=1

# 102 id=scoped-tls name=scoped-tls
mkdir -p "$CRATE_DOWNLOAD_DIR/102_scoped-tls"
wget -c "https://crates.io/api/v1/crates/scoped-tls/0.1.2/download" -O "$CRATE_DOWNLOAD_DIR/102_scoped-tls/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/102_scoped-tls/source"
tar -xf "$CRATE_DOWNLOAD_DIR/102_scoped-tls/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/102_scoped-tls/source" --strip-components=1

# 103 id=crossbeam-epoch name=crossbeam-epoch
mkdir -p "$CRATE_DOWNLOAD_DIR/103_crossbeam-epoch"
wget -c "https://crates.io/api/v1/crates/crossbeam-epoch/0.6.0/download" -O "$CRATE_DOWNLOAD_DIR/103_crossbeam-epoch/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/103_crossbeam-epoch/source"
tar -xf "$CRATE_DOWNLOAD_DIR/103_crossbeam-epoch/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/103_crossbeam-epoch/source" --strip-components=1

# 104 id=num-bigint name=num-bigint
mkdir -p "$CRATE_DOWNLOAD_DIR/104_num-bigint"
wget -c "https://crates.io/api/v1/crates/num-bigint/0.2.0/download" -O "$CRATE_DOWNLOAD_DIR/104_num-bigint/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/104_num-bigint/source"
tar -xf "$CRATE_DOWNLOAD_DIR/104_num-bigint/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/104_num-bigint/source" --strip-components=1

# 105 id=cmake name=cmake
mkdir -p "$CRATE_DOWNLOAD_DIR/105_cmake"
wget -c "https://crates.io/api/v1/crates/cmake/0.1.35/download" -O "$CRATE_DOWNLOAD_DIR/105_cmake/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/105_cmake/source"
tar -xf "$CRATE_DOWNLOAD_DIR/105_cmake/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/105_cmake/source" --strip-components=1

# 106 id=foreign-types name=foreign-types
mkdir -p "$CRATE_DOWNLOAD_DIR/106_foreign-types"
wget -c "https://crates.io/api/v1/crates/foreign-types/0.3.2/download" -O "$CRATE_DOWNLOAD_DIR/106_foreign-types/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/106_foreign-types/source"
tar -xf "$CRATE_DOWNLOAD_DIR/106_foreign-types/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/106_foreign-types/source" --strip-components=1

# 107 id=filetime name=filetime
mkdir -p "$CRATE_DOWNLOAD_DIR/107_filetime"
wget -c "https://crates.io/api/v1/crates/filetime/0.2.1/download" -O "$CRATE_DOWNLOAD_DIR/107_filetime/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/107_filetime/source"
tar -xf "$CRATE_DOWNLOAD_DIR/107_filetime/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/107_filetime/source" --strip-components=1

# 108 id=phf_shared name=phf_shared
mkdir -p "$CRATE_DOWNLOAD_DIR/108_phf_shared"
wget -c "https://crates.io/api/v1/crates/phf_shared/0.7.23/download" -O "$CRATE_DOWNLOAD_DIR/108_phf_shared/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/108_phf_shared/source"
tar -xf "$CRATE_DOWNLOAD_DIR/108_phf_shared/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/108_phf_shared/source" --strip-components=1

# 109 id=phf name=phf
mkdir -p "$CRATE_DOWNLOAD_DIR/109_phf"
wget -c "https://crates.io/api/v1/crates/phf/0.7.23/download" -O "$CRATE_DOWNLOAD_DIR/109_phf/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/109_phf/source"
tar -xf "$CRATE_DOWNLOAD_DIR/109_phf/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/109_phf/source" --strip-components=1

# 110 id=nix name=nix
mkdir -p "$CRATE_DOWNLOAD_DIR/110_nix"
wget -c "https://crates.io/api/v1/crates/nix/0.11.0/download" -O "$CRATE_DOWNLOAD_DIR/110_nix/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/110_nix/source"
tar -xf "$CRATE_DOWNLOAD_DIR/110_nix/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/110_nix/source" --strip-components=1

# 111 id=num-complex name=num-complex
mkdir -p "$CRATE_DOWNLOAD_DIR/111_num-complex"
wget -c "https://crates.io/api/v1/crates/num-complex/0.2.1/download" -O "$CRATE_DOWNLOAD_DIR/111_num-complex/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/111_num-complex/source"
tar -xf "$CRATE_DOWNLOAD_DIR/111_num-complex/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/111_num-complex/source" --strip-components=1

# 112 id=iovec name=iovec
mkdir -p "$CRATE_DOWNLOAD_DIR/112_iovec"
wget -c "https://crates.io/api/v1/crates/iovec/0.1.2/download" -O "$CRATE_DOWNLOAD_DIR/112_iovec/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/112_iovec/source"
tar -xf "$CRATE_DOWNLOAD_DIR/112_iovec/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/112_iovec/source" --strip-components=1

# 113 id=termcolor name=termcolor
mkdir -p "$CRATE_DOWNLOAD_DIR/113_termcolor"
wget -c "https://crates.io/api/v1/crates/termcolor/1.0.4/download" -O "$CRATE_DOWNLOAD_DIR/113_termcolor/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/113_termcolor/source"
tar -xf "$CRATE_DOWNLOAD_DIR/113_termcolor/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/113_termcolor/source" --strip-components=1

# 114 id=phf_generator name=phf_generator
mkdir -p "$CRATE_DOWNLOAD_DIR/114_phf_generator"
wget -c "https://crates.io/api/v1/crates/phf_generator/0.7.23/download" -O "$CRATE_DOWNLOAD_DIR/114_phf_generator/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/114_phf_generator/source"
tar -xf "$CRATE_DOWNLOAD_DIR/114_phf_generator/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/114_phf_generator/source" --strip-components=1

# 115 id=miow name=miow
mkdir -p "$CRATE_DOWNLOAD_DIR/115_miow"
wget -c "https://crates.io/api/v1/crates/miow/0.3.3/download" -O "$CRATE_DOWNLOAD_DIR/115_miow/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/115_miow/source"
tar -xf "$CRATE_DOWNLOAD_DIR/115_miow/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/115_miow/source" --strip-components=1

# 116 id=docopt name=docopt
mkdir -p "$CRATE_DOWNLOAD_DIR/116_docopt"
wget -c "https://crates.io/api/v1/crates/docopt/1.0.1/download" -O "$CRATE_DOWNLOAD_DIR/116_docopt/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/116_docopt/source"
tar -xf "$CRATE_DOWNLOAD_DIR/116_docopt/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/116_docopt/source" --strip-components=1

# 117 id=phf_codegen name=phf_codegen
mkdir -p "$CRATE_DOWNLOAD_DIR/117_phf_codegen"
wget -c "https://crates.io/api/v1/crates/phf_codegen/0.7.23/download" -O "$CRATE_DOWNLOAD_DIR/117_phf_codegen/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/117_phf_codegen/source"
tar -xf "$CRATE_DOWNLOAD_DIR/117_phf_codegen/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/117_phf_codegen/source" --strip-components=1

# 118 id=safemem name=safemem
mkdir -p "$CRATE_DOWNLOAD_DIR/118_safemem"
wget -c "https://crates.io/api/v1/crates/safemem/0.3.0/download" -O "$CRATE_DOWNLOAD_DIR/118_safemem/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/118_safemem/source"
tar -xf "$CRATE_DOWNLOAD_DIR/118_safemem/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/118_safemem/source" --strip-components=1

# 119 id=cookie name=cookie
mkdir -p "$CRATE_DOWNLOAD_DIR/119_cookie"
wget -c "https://crates.io/api/v1/crates/cookie/0.11.0/download" -O "$CRATE_DOWNLOAD_DIR/119_cookie/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/119_cookie/source"
tar -xf "$CRATE_DOWNLOAD_DIR/119_cookie/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/119_cookie/source" --strip-components=1

# 120 id=crossbeam-deque name=crossbeam-deque
mkdir -p "$CRATE_DOWNLOAD_DIR/120_crossbeam-deque"
wget -c "https://crates.io/api/v1/crates/crossbeam-deque/0.6.1/download" -O "$CRATE_DOWNLOAD_DIR/120_crossbeam-deque/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/120_crossbeam-deque/source"
tar -xf "$CRATE_DOWNLOAD_DIR/120_crossbeam-deque/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/120_crossbeam-deque/source" --strip-components=1

# 121 id=syntex_pos name=syntex_pos
mkdir -p "$CRATE_DOWNLOAD_DIR/121_syntex_pos"
wget -c "https://crates.io/api/v1/crates/syntex_pos/0.59.1/download" -O "$CRATE_DOWNLOAD_DIR/121_syntex_pos/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/121_syntex_pos/source"
tar -xf "$CRATE_DOWNLOAD_DIR/121_syntex_pos/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/121_syntex_pos/source" --strip-components=1

# 122 id=same-file name=same-file
mkdir -p "$CRATE_DOWNLOAD_DIR/122_same-file"
wget -c "https://crates.io/api/v1/crates/same-file/1.0.3/download" -O "$CRATE_DOWNLOAD_DIR/122_same-file/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/122_same-file/source"
tar -xf "$CRATE_DOWNLOAD_DIR/122_same-file/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/122_same-file/source" --strip-components=1

# 123 id=syntex_errors name=syntex_errors
mkdir -p "$CRATE_DOWNLOAD_DIR/123_syntex_errors"
wget -c "https://crates.io/api/v1/crates/syntex_errors/0.59.1/download" -O "$CRATE_DOWNLOAD_DIR/123_syntex_errors/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/123_syntex_errors/source"
tar -xf "$CRATE_DOWNLOAD_DIR/123_syntex_errors/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/123_syntex_errors/source" --strip-components=1

# 124 id=ucd-util name=ucd-util
mkdir -p "$CRATE_DOWNLOAD_DIR/124_ucd-util"
wget -c "https://crates.io/api/v1/crates/ucd-util/0.1.1/download" -O "$CRATE_DOWNLOAD_DIR/124_ucd-util/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/124_ucd-util/source"
tar -xf "$CRATE_DOWNLOAD_DIR/124_ucd-util/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/124_ucd-util/source" --strip-components=1

# 125 id=siphasher name=siphasher
mkdir -p "$CRATE_DOWNLOAD_DIR/125_siphasher"
wget -c "https://crates.io/api/v1/crates/siphasher/0.2.3/download" -O "$CRATE_DOWNLOAD_DIR/125_siphasher/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/125_siphasher/source"
tar -xf "$CRATE_DOWNLOAD_DIR/125_siphasher/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/125_siphasher/source" --strip-components=1

# 126 id=curl-sys name=curl-sys
mkdir -p "$CRATE_DOWNLOAD_DIR/126_curl-sys"
wget -c "https://crates.io/api/v1/crates/curl-sys/0.4.13/download" -O "$CRATE_DOWNLOAD_DIR/126_curl-sys/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/126_curl-sys/source"
tar -xf "$CRATE_DOWNLOAD_DIR/126_curl-sys/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/126_curl-sys/source" --strip-components=1

# 127 id=xml-rs name=xml-rs
mkdir -p "$CRATE_DOWNLOAD_DIR/127_xml-rs"
wget -c "https://crates.io/api/v1/crates/xml-rs/0.8.0/download" -O "$CRATE_DOWNLOAD_DIR/127_xml-rs/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/127_xml-rs/source"
tar -xf "$CRATE_DOWNLOAD_DIR/127_xml-rs/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/127_xml-rs/source" --strip-components=1

# 128 id=rayon-core name=rayon-core
mkdir -p "$CRATE_DOWNLOAD_DIR/128_rayon-core"
wget -c "https://crates.io/api/v1/crates/rayon-core/1.4.1/download" -O "$CRATE_DOWNLOAD_DIR/128_rayon-core/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/128_rayon-core/source"
tar -xf "$CRATE_DOWNLOAD_DIR/128_rayon-core/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/128_rayon-core/source" --strip-components=1

# 129 id=pulldown-cmark name=pulldown-cmark
mkdir -p "$CRATE_DOWNLOAD_DIR/129_pulldown-cmark"
wget -c "https://crates.io/api/v1/crates/pulldown-cmark/0.1.2/download" -O "$CRATE_DOWNLOAD_DIR/129_pulldown-cmark/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/129_pulldown-cmark/source"
tar -xf "$CRATE_DOWNLOAD_DIR/129_pulldown-cmark/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/129_pulldown-cmark/source" --strip-components=1

# 130 id=linked-hash-map name=linked-hash-map
mkdir -p "$CRATE_DOWNLOAD_DIR/130_linked-hash-map"
wget -c "https://crates.io/api/v1/crates/linked-hash-map/0.5.1/download" -O "$CRATE_DOWNLOAD_DIR/130_linked-hash-map/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/130_linked-hash-map/source"
tar -xf "$CRATE_DOWNLOAD_DIR/130_linked-hash-map/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/130_linked-hash-map/source" --strip-components=1

# 131 id=tokio-io name=tokio-io
mkdir -p "$CRATE_DOWNLOAD_DIR/131_tokio-io"
wget -c "https://crates.io/api/v1/crates/tokio-io/0.1.9/download" -O "$CRATE_DOWNLOAD_DIR/131_tokio-io/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/131_tokio-io/source"
tar -xf "$CRATE_DOWNLOAD_DIR/131_tokio-io/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/131_tokio-io/source" --strip-components=1

# 132 id=curl name=curl
mkdir -p "$CRATE_DOWNLOAD_DIR/132_curl"
wget -c "https://crates.io/api/v1/crates/curl/0.4.18/download" -O "$CRATE_DOWNLOAD_DIR/132_curl/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/132_curl/source"
tar -xf "$CRATE_DOWNLOAD_DIR/132_curl/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/132_curl/source" --strip-components=1

# 133 id=parking_lot name=parking_lot
mkdir -p "$CRATE_DOWNLOAD_DIR/133_parking_lot"
wget -c "https://crates.io/api/v1/crates/parking_lot/0.6.4/download" -O "$CRATE_DOWNLOAD_DIR/133_parking_lot/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/133_parking_lot/source"
tar -xf "$CRATE_DOWNLOAD_DIR/133_parking_lot/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/133_parking_lot/source" --strip-components=1

# 134 id=hex name=hex
mkdir -p "$CRATE_DOWNLOAD_DIR/134_hex"
wget -c "https://crates.io/api/v1/crates/hex/0.3.2/download" -O "$CRATE_DOWNLOAD_DIR/134_hex/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/134_hex/source"
tar -xf "$CRATE_DOWNLOAD_DIR/134_hex/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/134_hex/source" --strip-components=1

# 135 id=term_size name=term_size
mkdir -p "$CRATE_DOWNLOAD_DIR/135_term_size"
wget -c "https://crates.io/api/v1/crates/term_size/1.0.0-beta1/download" -O "$CRATE_DOWNLOAD_DIR/135_term_size/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/135_term_size/source"
tar -xf "$CRATE_DOWNLOAD_DIR/135_term_size/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/135_term_size/source" --strip-components=1

# 136 id=ws2_32-sys name=ws2_32-sys
mkdir -p "$CRATE_DOWNLOAD_DIR/136_ws2_32-sys"
wget -c "https://crates.io/api/v1/crates/ws2_32-sys/0.2.1/download" -O "$CRATE_DOWNLOAD_DIR/136_ws2_32-sys/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/136_ws2_32-sys/source"
tar -xf "$CRATE_DOWNLOAD_DIR/136_ws2_32-sys/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/136_ws2_32-sys/source" --strip-components=1

# 137 id=memoffset name=memoffset
mkdir -p "$CRATE_DOWNLOAD_DIR/137_memoffset"
wget -c "https://crates.io/api/v1/crates/memoffset/0.2.1/download" -O "$CRATE_DOWNLOAD_DIR/137_memoffset/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/137_memoffset/source"
tar -xf "$CRATE_DOWNLOAD_DIR/137_memoffset/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/137_memoffset/source" --strip-components=1

# 138 id=owning_ref name=owning_ref
mkdir -p "$CRATE_DOWNLOAD_DIR/138_owning_ref"
wget -c "https://crates.io/api/v1/crates/owning_ref/0.4.0/download" -O "$CRATE_DOWNLOAD_DIR/138_owning_ref/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/138_owning_ref/source"
tar -xf "$CRATE_DOWNLOAD_DIR/138_owning_ref/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/138_owning_ref/source" --strip-components=1

# 139 id=advapi32-sys name=advapi32-sys
mkdir -p "$CRATE_DOWNLOAD_DIR/139_advapi32-sys"
wget -c "https://crates.io/api/v1/crates/advapi32-sys/0.2.0/download" -O "$CRATE_DOWNLOAD_DIR/139_advapi32-sys/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/139_advapi32-sys/source"
tar -xf "$CRATE_DOWNLOAD_DIR/139_advapi32-sys/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/139_advapi32-sys/source" --strip-components=1

# 140 id=parking_lot_core name=parking_lot_core
mkdir -p "$CRATE_DOWNLOAD_DIR/140_parking_lot_core"
wget -c "https://crates.io/api/v1/crates/parking_lot_core/0.3.1/download" -O "$CRATE_DOWNLOAD_DIR/140_parking_lot_core/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/140_parking_lot_core/source"
tar -xf "$CRATE_DOWNLOAD_DIR/140_parking_lot_core/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/140_parking_lot_core/source" --strip-components=1

# 141 id=stable_deref_trait name=stable_deref_trait
mkdir -p "$CRATE_DOWNLOAD_DIR/141_stable_deref_trait"
wget -c "https://crates.io/api/v1/crates/stable_deref_trait/1.1.1/download" -O "$CRATE_DOWNLOAD_DIR/141_stable_deref_trait/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/141_stable_deref_trait/source"
tar -xf "$CRATE_DOWNLOAD_DIR/141_stable_deref_trait/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/141_stable_deref_trait/source" --strip-components=1

# 142 id=tokio-core name=tokio-core
mkdir -p "$CRATE_DOWNLOAD_DIR/142_tokio-core"
wget -c "https://crates.io/api/v1/crates/tokio-core/0.1.17/download" -O "$CRATE_DOWNLOAD_DIR/142_tokio-core/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/142_tokio-core/source"
tar -xf "$CRATE_DOWNLOAD_DIR/142_tokio-core/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/142_tokio-core/source" --strip-components=1

# 143 id=tempfile name=tempfile
mkdir -p "$CRATE_DOWNLOAD_DIR/143_tempfile"
wget -c "https://crates.io/api/v1/crates/tempfile/3.0.4/download" -O "$CRATE_DOWNLOAD_DIR/143_tempfile/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/143_tempfile/source"
tar -xf "$CRATE_DOWNLOAD_DIR/143_tempfile/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/143_tempfile/source" --strip-components=1

# 144 id=fs2 name=fs2
mkdir -p "$CRATE_DOWNLOAD_DIR/144_fs2"
wget -c "https://crates.io/api/v1/crates/fs2/0.4.3/download" -O "$CRATE_DOWNLOAD_DIR/144_fs2/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/144_fs2/source"
tar -xf "$CRATE_DOWNLOAD_DIR/144_fs2/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/144_fs2/source" --strip-components=1

# 145 id=libgit2-sys name=libgit2-sys
mkdir -p "$CRATE_DOWNLOAD_DIR/145_libgit2-sys"
wget -c "https://crates.io/api/v1/crates/libgit2-sys/0.7.10/download" -O "$CRATE_DOWNLOAD_DIR/145_libgit2-sys/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/145_libgit2-sys/source"
tar -xf "$CRATE_DOWNLOAD_DIR/145_libgit2-sys/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/145_libgit2-sys/source" --strip-components=1

# 146 id=yaml-rust name=yaml-rust
mkdir -p "$CRATE_DOWNLOAD_DIR/146_yaml-rust"
wget -c "https://crates.io/api/v1/crates/yaml-rust/0.4.2/download" -O "$CRATE_DOWNLOAD_DIR/146_yaml-rust/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/146_yaml-rust/source"
tar -xf "$CRATE_DOWNLOAD_DIR/146_yaml-rust/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/146_yaml-rust/source" --strip-components=1

# 147 id=git2 name=git2
mkdir -p "$CRATE_DOWNLOAD_DIR/147_git2"
wget -c "https://crates.io/api/v1/crates/git2/0.7.5/download" -O "$CRATE_DOWNLOAD_DIR/147_git2/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/147_git2/source"
tar -xf "$CRATE_DOWNLOAD_DIR/147_git2/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/147_git2/source" --strip-components=1

# 148 id=nom name=nom
mkdir -p "$CRATE_DOWNLOAD_DIR/148_nom"
wget -c "https://crates.io/api/v1/crates/nom/4.1.1/download" -O "$CRATE_DOWNLOAD_DIR/148_nom/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/148_nom/source"
tar -xf "$CRATE_DOWNLOAD_DIR/148_nom/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/148_nom/source" --strip-components=1

# 149 id=openssl-probe name=openssl-probe
mkdir -p "$CRATE_DOWNLOAD_DIR/149_openssl-probe"
wget -c "https://crates.io/api/v1/crates/openssl-probe/0.1.2/download" -O "$CRATE_DOWNLOAD_DIR/149_openssl-probe/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/149_openssl-probe/source"
tar -xf "$CRATE_DOWNLOAD_DIR/149_openssl-probe/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/149_openssl-probe/source" --strip-components=1

# 150 id=remove_dir_all name=remove_dir_all
mkdir -p "$CRATE_DOWNLOAD_DIR/150_remove_dir_all"
wget -c "https://crates.io/api/v1/crates/remove_dir_all/0.5.1/download" -O "$CRATE_DOWNLOAD_DIR/150_remove_dir_all/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/150_remove_dir_all/source"
tar -xf "$CRATE_DOWNLOAD_DIR/150_remove_dir_all/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/150_remove_dir_all/source" --strip-components=1

# 151 id=tar name=tar
mkdir -p "$CRATE_DOWNLOAD_DIR/151_tar"
wget -c "https://crates.io/api/v1/crates/tar/0.4.17/download" -O "$CRATE_DOWNLOAD_DIR/151_tar/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/151_tar/source"
tar -xf "$CRATE_DOWNLOAD_DIR/151_tar/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/151_tar/source" --strip-components=1

# 152 id=humantime name=humantime
mkdir -p "$CRATE_DOWNLOAD_DIR/152_humantime"
wget -c "https://crates.io/api/v1/crates/humantime/1.1.1/download" -O "$CRATE_DOWNLOAD_DIR/152_humantime/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/152_humantime/source"
tar -xf "$CRATE_DOWNLOAD_DIR/152_humantime/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/152_humantime/source" --strip-components=1

# 153 id=synstructure name=synstructure
mkdir -p "$CRATE_DOWNLOAD_DIR/153_synstructure"
wget -c "https://crates.io/api/v1/crates/synstructure/0.10.0/download" -O "$CRATE_DOWNLOAD_DIR/153_synstructure/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/153_synstructure/source"
tar -xf "$CRATE_DOWNLOAD_DIR/153_synstructure/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/153_synstructure/source" --strip-components=1

# 154 id=redox_syscall name=redox_syscall
mkdir -p "$CRATE_DOWNLOAD_DIR/154_redox_syscall"
wget -c "https://crates.io/api/v1/crates/redox_syscall/0.1.40/download" -O "$CRATE_DOWNLOAD_DIR/154_redox_syscall/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/154_redox_syscall/source"
tar -xf "$CRATE_DOWNLOAD_DIR/154_redox_syscall/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/154_redox_syscall/source" --strip-components=1

# 155 id=libssh2-sys name=libssh2-sys
mkdir -p "$CRATE_DOWNLOAD_DIR/155_libssh2-sys"
wget -c "https://crates.io/api/v1/crates/libssh2-sys/0.2.11/download" -O "$CRATE_DOWNLOAD_DIR/155_libssh2-sys/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/155_libssh2-sys/source"
tar -xf "$CRATE_DOWNLOAD_DIR/155_libssh2-sys/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/155_libssh2-sys/source" --strip-components=1

# 156 id=foreign-types-shared name=foreign-types-shared
mkdir -p "$CRATE_DOWNLOAD_DIR/156_foreign-types-shared"
wget -c "https://crates.io/api/v1/crates/foreign-types-shared/0.1.1/download" -O "$CRATE_DOWNLOAD_DIR/156_foreign-types-shared/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/156_foreign-types-shared/source"
tar -xf "$CRATE_DOWNLOAD_DIR/156_foreign-types-shared/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/156_foreign-types-shared/source" --strip-components=1

# 157 id=futures-cpupool name=futures-cpupool
mkdir -p "$CRATE_DOWNLOAD_DIR/157_futures-cpupool"
wget -c "https://crates.io/api/v1/crates/futures-cpupool/0.1.8/download" -O "$CRATE_DOWNLOAD_DIR/157_futures-cpupool/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/157_futures-cpupool/source"
tar -xf "$CRATE_DOWNLOAD_DIR/157_futures-cpupool/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/157_futures-cpupool/source" --strip-components=1

# 158 id=enum_primitive name=enum_primitive
mkdir -p "$CRATE_DOWNLOAD_DIR/158_enum_primitive"
wget -c "https://crates.io/api/v1/crates/enum_primitive/0.1.1/download" -O "$CRATE_DOWNLOAD_DIR/158_enum_primitive/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/158_enum_primitive/source"
tar -xf "$CRATE_DOWNLOAD_DIR/158_enum_primitive/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/158_enum_primitive/source" --strip-components=1

# 159 id=failure name=failure
mkdir -p "$CRATE_DOWNLOAD_DIR/159_failure"
wget -c "https://crates.io/api/v1/crates/failure/0.1.3/download" -O "$CRATE_DOWNLOAD_DIR/159_failure/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/159_failure/source"
tar -xf "$CRATE_DOWNLOAD_DIR/159_failure/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/159_failure/source" --strip-components=1

# 160 id=failure_derive name=failure_derive
mkdir -p "$CRATE_DOWNLOAD_DIR/160_failure_derive"
wget -c "https://crates.io/api/v1/crates/failure_derive/0.1.3/download" -O "$CRATE_DOWNLOAD_DIR/160_failure_derive/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/160_failure_derive/source"
tar -xf "$CRATE_DOWNLOAD_DIR/160_failure_derive/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/160_failure_derive/source" --strip-components=1

# 161 id=solicit name=solicit
mkdir -p "$CRATE_DOWNLOAD_DIR/161_solicit"
wget -c "https://crates.io/api/v1/crates/solicit/0.4.4/download" -O "$CRATE_DOWNLOAD_DIR/161_solicit/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/161_solicit/source"
tar -xf "$CRATE_DOWNLOAD_DIR/161_solicit/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/161_solicit/source" --strip-components=1

# 162 id=hpack name=hpack
mkdir -p "$CRATE_DOWNLOAD_DIR/162_hpack"
wget -c "https://crates.io/api/v1/crates/hpack/0.3.0/download" -O "$CRATE_DOWNLOAD_DIR/162_hpack/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/162_hpack/source"
tar -xf "$CRATE_DOWNLOAD_DIR/162_hpack/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/162_hpack/source" --strip-components=1

# 163 id=rust-crypto name=rust-crypto
mkdir -p "$CRATE_DOWNLOAD_DIR/163_rust-crypto"
wget -c "https://crates.io/api/v1/crates/rust-crypto/0.2.36/download" -O "$CRATE_DOWNLOAD_DIR/163_rust-crypto/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/163_rust-crypto/source"
tar -xf "$CRATE_DOWNLOAD_DIR/163_rust-crypto/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/163_rust-crypto/source" --strip-components=1

# 164 id=serde_codegen_internals name=serde_codegen_internals
mkdir -p "$CRATE_DOWNLOAD_DIR/164_serde_codegen_internals"
wget -c "https://crates.io/api/v1/crates/serde_codegen_internals/0.14.2/download" -O "$CRATE_DOWNLOAD_DIR/164_serde_codegen_internals/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/164_serde_codegen_internals/source"
tar -xf "$CRATE_DOWNLOAD_DIR/164_serde_codegen_internals/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/164_serde_codegen_internals/source" --strip-components=1

# 165 id=core-foundation name=core-foundation
mkdir -p "$CRATE_DOWNLOAD_DIR/165_core-foundation"
wget -c "https://crates.io/api/v1/crates/core-foundation/0.6.2/download" -O "$CRATE_DOWNLOAD_DIR/165_core-foundation/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/165_core-foundation/source"
tar -xf "$CRATE_DOWNLOAD_DIR/165_core-foundation/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/165_core-foundation/source" --strip-components=1

# 166 id=core-foundation-sys name=core-foundation-sys
mkdir -p "$CRATE_DOWNLOAD_DIR/166_core-foundation-sys"
wget -c "https://crates.io/api/v1/crates/core-foundation-sys/0.6.2/download" -O "$CRATE_DOWNLOAD_DIR/166_core-foundation-sys/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/166_core-foundation-sys/source"
tar -xf "$CRATE_DOWNLOAD_DIR/166_core-foundation-sys/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/166_core-foundation-sys/source" --strip-components=1

# 167 id=socket2 name=socket2
mkdir -p "$CRATE_DOWNLOAD_DIR/167_socket2"
wget -c "https://crates.io/api/v1/crates/socket2/0.3.8/download" -O "$CRATE_DOWNLOAD_DIR/167_socket2/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/167_socket2/source"
tar -xf "$CRATE_DOWNLOAD_DIR/167_socket2/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/167_socket2/source" --strip-components=1

# 168 id=adler32 name=adler32
mkdir -p "$CRATE_DOWNLOAD_DIR/168_adler32"
wget -c "https://crates.io/api/v1/crates/adler32/1.0.3/download" -O "$CRATE_DOWNLOAD_DIR/168_adler32/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/168_adler32/source"
tar -xf "$CRATE_DOWNLOAD_DIR/168_adler32/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/168_adler32/source" --strip-components=1

# 169 id=tokio-timer name=tokio-timer
mkdir -p "$CRATE_DOWNLOAD_DIR/169_tokio-timer"
wget -c "https://crates.io/api/v1/crates/tokio-timer/0.2.7/download" -O "$CRATE_DOWNLOAD_DIR/169_tokio-timer/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/169_tokio-timer/source"
tar -xf "$CRATE_DOWNLOAD_DIR/169_tokio-timer/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/169_tokio-timer/source" --strip-components=1

# 170 id=native-tls name=native-tls
mkdir -p "$CRATE_DOWNLOAD_DIR/170_native-tls"
wget -c "https://crates.io/api/v1/crates/native-tls/0.2.2/download" -O "$CRATE_DOWNLOAD_DIR/170_native-tls/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/170_native-tls/source"
tar -xf "$CRATE_DOWNLOAD_DIR/170_native-tls/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/170_native-tls/source" --strip-components=1

# 171 id=cargo_metadata name=cargo_metadata
mkdir -p "$CRATE_DOWNLOAD_DIR/171_cargo_metadata"
wget -c "https://crates.io/api/v1/crates/cargo_metadata/0.6.1/download" -O "$CRATE_DOWNLOAD_DIR/171_cargo_metadata/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/171_cargo_metadata/source"
tar -xf "$CRATE_DOWNLOAD_DIR/171_cargo_metadata/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/171_cargo_metadata/source" --strip-components=1

# 172 id=handlebars name=handlebars
mkdir -p "$CRATE_DOWNLOAD_DIR/172_handlebars"
wget -c "https://crates.io/api/v1/crates/handlebars/1.0.5/download" -O "$CRATE_DOWNLOAD_DIR/172_handlebars/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/172_handlebars/source"
tar -xf "$CRATE_DOWNLOAD_DIR/172_handlebars/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/172_handlebars/source" --strip-components=1

# 173 id=pest name=pest
mkdir -p "$CRATE_DOWNLOAD_DIR/173_pest"
wget -c "https://crates.io/api/v1/crates/pest/2.0.2/download" -O "$CRATE_DOWNLOAD_DIR/173_pest/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/173_pest/source"
tar -xf "$CRATE_DOWNLOAD_DIR/173_pest/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/173_pest/source" --strip-components=1

# 174 id=rand_core name=rand_core
mkdir -p "$CRATE_DOWNLOAD_DIR/174_rand_core"
wget -c "https://crates.io/api/v1/crates/rand_core/0.3.0/download" -O "$CRATE_DOWNLOAD_DIR/174_rand_core/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/174_rand_core/source"
tar -xf "$CRATE_DOWNLOAD_DIR/174_rand_core/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/174_rand_core/source" --strip-components=1

# 175 id=globset name=globset
mkdir -p "$CRATE_DOWNLOAD_DIR/175_globset"
wget -c "https://crates.io/api/v1/crates/globset/0.4.2/download" -O "$CRATE_DOWNLOAD_DIR/175_globset/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/175_globset/source"
tar -xf "$CRATE_DOWNLOAD_DIR/175_globset/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/175_globset/source" --strip-components=1

# 176 id=diff name=diff
mkdir -p "$CRATE_DOWNLOAD_DIR/176_diff"
wget -c "https://crates.io/api/v1/crates/diff/0.1.11/download" -O "$CRATE_DOWNLOAD_DIR/176_diff/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/176_diff/source"
tar -xf "$CRATE_DOWNLOAD_DIR/176_diff/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/176_diff/source" --strip-components=1

# 177 id=gl_generator name=gl_generator
mkdir -p "$CRATE_DOWNLOAD_DIR/177_gl_generator"
wget -c "https://crates.io/api/v1/crates/gl_generator/0.9.0/download" -O "$CRATE_DOWNLOAD_DIR/177_gl_generator/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/177_gl_generator/source"
tar -xf "$CRATE_DOWNLOAD_DIR/177_gl_generator/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/177_gl_generator/source" --strip-components=1

# 178 id=wincolor name=wincolor
mkdir -p "$CRATE_DOWNLOAD_DIR/178_wincolor"
wget -c "https://crates.io/api/v1/crates/wincolor/1.0.1/download" -O "$CRATE_DOWNLOAD_DIR/178_wincolor/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/178_wincolor/source"
tar -xf "$CRATE_DOWNLOAD_DIR/178_wincolor/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/178_wincolor/source" --strip-components=1

# 179 id=syntex name=syntex
mkdir -p "$CRATE_DOWNLOAD_DIR/179_syntex"
wget -c "https://crates.io/api/v1/crates/syntex/0.58.1/download" -O "$CRATE_DOWNLOAD_DIR/179_syntex/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/179_syntex/source"
tar -xf "$CRATE_DOWNLOAD_DIR/179_syntex/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/179_syntex/source" --strip-components=1

# 180 id=untrusted name=untrusted
mkdir -p "$CRATE_DOWNLOAD_DIR/180_untrusted"
wget -c "https://crates.io/api/v1/crates/untrusted/0.6.2/download" -O "$CRATE_DOWNLOAD_DIR/180_untrusted/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/180_untrusted/source"
tar -xf "$CRATE_DOWNLOAD_DIR/180_untrusted/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/180_untrusted/source" --strip-components=1

# 181 id=tokio-service name=tokio-service
mkdir -p "$CRATE_DOWNLOAD_DIR/181_tokio-service"
wget -c "https://crates.io/api/v1/crates/tokio-service/0.1.0/download" -O "$CRATE_DOWNLOAD_DIR/181_tokio-service/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/181_tokio-service/source"
tar -xf "$CRATE_DOWNLOAD_DIR/181_tokio-service/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/181_tokio-service/source" --strip-components=1

# 182 id=dbghelp-sys name=dbghelp-sys
mkdir -p "$CRATE_DOWNLOAD_DIR/182_dbghelp-sys"
wget -c "https://crates.io/api/v1/crates/dbghelp-sys/0.2.0/download" -O "$CRATE_DOWNLOAD_DIR/182_dbghelp-sys/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/182_dbghelp-sys/source"
tar -xf "$CRATE_DOWNLOAD_DIR/182_dbghelp-sys/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/182_dbghelp-sys/source" --strip-components=1

# 183 id=bufstream name=bufstream
mkdir -p "$CRATE_DOWNLOAD_DIR/183_bufstream"
wget -c "https://crates.io/api/v1/crates/bufstream/0.1.4/download" -O "$CRATE_DOWNLOAD_DIR/183_bufstream/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/183_bufstream/source"
tar -xf "$CRATE_DOWNLOAD_DIR/183_bufstream/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/183_bufstream/source" --strip-components=1

# 184 id=git2-curl name=git2-curl
mkdir -p "$CRATE_DOWNLOAD_DIR/184_git2-curl"
wget -c "https://crates.io/api/v1/crates/git2-curl/0.8.2/download" -O "$CRATE_DOWNLOAD_DIR/184_git2-curl/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/184_git2-curl/source"
tar -xf "$CRATE_DOWNLOAD_DIR/184_git2-curl/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/184_git2-curl/source" --strip-components=1

# 185 id=serde_codegen name=serde_codegen
mkdir -p "$CRATE_DOWNLOAD_DIR/185_serde_codegen"
wget -c "https://crates.io/api/v1/crates/serde_codegen/0.9.0/download" -O "$CRATE_DOWNLOAD_DIR/185_serde_codegen/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/185_serde_codegen/source"
tar -xf "$CRATE_DOWNLOAD_DIR/185_serde_codegen/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/185_serde_codegen/source" --strip-components=1

# 186 id=take name=take
mkdir -p "$CRATE_DOWNLOAD_DIR/186_take"
wget -c "https://crates.io/api/v1/crates/take/0.1.0/download" -O "$CRATE_DOWNLOAD_DIR/186_take/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/186_take/source"
tar -xf "$CRATE_DOWNLOAD_DIR/186_take/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/186_take/source" --strip-components=1

# 187 id=ordermap name=ordermap
mkdir -p "$CRATE_DOWNLOAD_DIR/187_ordermap"
wget -c "https://crates.io/api/v1/crates/ordermap/0.4.1/download" -O "$CRATE_DOWNLOAD_DIR/187_ordermap/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/187_ordermap/source"
tar -xf "$CRATE_DOWNLOAD_DIR/187_ordermap/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/187_ordermap/source" --strip-components=1

# 188 id=khronos_api name=khronos_api
mkdir -p "$CRATE_DOWNLOAD_DIR/188_khronos_api"
wget -c "https://crates.io/api/v1/crates/khronos_api/2.2.0/download" -O "$CRATE_DOWNLOAD_DIR/188_khronos_api/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/188_khronos_api/source"
tar -xf "$CRATE_DOWNLOAD_DIR/188_khronos_api/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/188_khronos_api/source" --strip-components=1

# 189 id=vcpkg name=vcpkg
mkdir -p "$CRATE_DOWNLOAD_DIR/189_vcpkg"
wget -c "https://crates.io/api/v1/crates/vcpkg/0.2.6/download" -O "$CRATE_DOWNLOAD_DIR/189_vcpkg/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/189_vcpkg/source"
tar -xf "$CRATE_DOWNLOAD_DIR/189_vcpkg/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/189_vcpkg/source" --strip-components=1

# 190 id=user32-sys name=user32-sys
mkdir -p "$CRATE_DOWNLOAD_DIR/190_user32-sys"
wget -c "https://crates.io/api/v1/crates/user32-sys/0.2.0/download" -O "$CRATE_DOWNLOAD_DIR/190_user32-sys/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/190_user32-sys/source"
tar -xf "$CRATE_DOWNLOAD_DIR/190_user32-sys/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/190_user32-sys/source" --strip-components=1

# 191 id=tokio-proto name=tokio-proto
mkdir -p "$CRATE_DOWNLOAD_DIR/191_tokio-proto"
wget -c "https://crates.io/api/v1/crates/tokio-proto/0.1.1/download" -O "$CRATE_DOWNLOAD_DIR/191_tokio-proto/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/191_tokio-proto/source"
tar -xf "$CRATE_DOWNLOAD_DIR/191_tokio-proto/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/191_tokio-proto/source" --strip-components=1

# 192 id=ignore name=ignore
mkdir -p "$CRATE_DOWNLOAD_DIR/192_ignore"
wget -c "https://crates.io/api/v1/crates/ignore/0.4.4/download" -O "$CRATE_DOWNLOAD_DIR/192_ignore/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/192_ignore/source"
tar -xf "$CRATE_DOWNLOAD_DIR/192_ignore/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/192_ignore/source" --strip-components=1

# 193 id=memmap name=memmap
mkdir -p "$CRATE_DOWNLOAD_DIR/193_memmap"
wget -c "https://crates.io/api/v1/crates/memmap/0.7.0/download" -O "$CRATE_DOWNLOAD_DIR/193_memmap/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/193_memmap/source"
tar -xf "$CRATE_DOWNLOAD_DIR/193_memmap/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/193_memmap/source" --strip-components=1

# 194 id=serde_ignored name=serde_ignored
mkdir -p "$CRATE_DOWNLOAD_DIR/194_serde_ignored"
wget -c "https://crates.io/api/v1/crates/serde_ignored/0.0.4/download" -O "$CRATE_DOWNLOAD_DIR/194_serde_ignored/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/194_serde_ignored/source"
tar -xf "$CRATE_DOWNLOAD_DIR/194_serde_ignored/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/194_serde_ignored/source" --strip-components=1

# 195 id=fuchsia-zircon name=fuchsia-zircon
mkdir -p "$CRATE_DOWNLOAD_DIR/195_fuchsia-zircon"
wget -c "https://crates.io/api/v1/crates/fuchsia-zircon/0.3.3/download" -O "$CRATE_DOWNLOAD_DIR/195_fuchsia-zircon/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/195_fuchsia-zircon/source"
tar -xf "$CRATE_DOWNLOAD_DIR/195_fuchsia-zircon/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/195_fuchsia-zircon/source" --strip-components=1

# 196 id=fuchsia-zircon-sys name=fuchsia-zircon-sys
mkdir -p "$CRATE_DOWNLOAD_DIR/196_fuchsia-zircon-sys"
wget -c "https://crates.io/api/v1/crates/fuchsia-zircon-sys/0.3.3/download" -O "$CRATE_DOWNLOAD_DIR/196_fuchsia-zircon-sys/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/196_fuchsia-zircon-sys/source"
tar -xf "$CRATE_DOWNLOAD_DIR/196_fuchsia-zircon-sys/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/196_fuchsia-zircon-sys/source" --strip-components=1

# 197 id=racer name=racer
mkdir -p "$CRATE_DOWNLOAD_DIR/197_racer"
wget -c "https://crates.io/api/v1/crates/racer/2.1.9/download" -O "$CRATE_DOWNLOAD_DIR/197_racer/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/197_racer/source"
tar -xf "$CRATE_DOWNLOAD_DIR/197_racer/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/197_racer/source" --strip-components=1

# 198 id=tokio-reactor name=tokio-reactor
mkdir -p "$CRATE_DOWNLOAD_DIR/198_tokio-reactor"
wget -c "https://crates.io/api/v1/crates/tokio-reactor/0.1.6/download" -O "$CRATE_DOWNLOAD_DIR/198_tokio-reactor/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/198_tokio-reactor/source"
tar -xf "$CRATE_DOWNLOAD_DIR/198_tokio-reactor/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/198_tokio-reactor/source" --strip-components=1

# 199 id=tokio-threadpool name=tokio-threadpool
mkdir -p "$CRATE_DOWNLOAD_DIR/199_tokio-threadpool"
wget -c "https://crates.io/api/v1/crates/tokio-threadpool/0.1.7/download" -O "$CRATE_DOWNLOAD_DIR/199_tokio-threadpool/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/199_tokio-threadpool/source"
tar -xf "$CRATE_DOWNLOAD_DIR/199_tokio-threadpool/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/199_tokio-threadpool/source" --strip-components=1

# 200 id=tokio name=tokio
mkdir -p "$CRATE_DOWNLOAD_DIR/200_tokio"
wget -c "https://crates.io/api/v1/crates/tokio/0.1.11/download" -O "$CRATE_DOWNLOAD_DIR/200_tokio/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/200_tokio/source"
tar -xf "$CRATE_DOWNLOAD_DIR/200_tokio/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/200_tokio/source" --strip-components=1

# 201 id=serde_urlencoded name=serde_urlencoded
mkdir -p "$CRATE_DOWNLOAD_DIR/201_serde_urlencoded"
wget -c "https://crates.io/api/v1/crates/serde_urlencoded/0.5.3/download" -O "$CRATE_DOWNLOAD_DIR/201_serde_urlencoded/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/201_serde_urlencoded/source"
tar -xf "$CRATE_DOWNLOAD_DIR/201_serde_urlencoded/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/201_serde_urlencoded/source" --strip-components=1

# 202 id=gdi32-sys name=gdi32-sys
mkdir -p "$CRATE_DOWNLOAD_DIR/202_gdi32-sys"
wget -c "https://crates.io/api/v1/crates/gdi32-sys/0.2.0/download" -O "$CRATE_DOWNLOAD_DIR/202_gdi32-sys/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/202_gdi32-sys/source"
tar -xf "$CRATE_DOWNLOAD_DIR/202_gdi32-sys/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/202_gdi32-sys/source" --strip-components=1

# 203 id=shell-escape name=shell-escape
mkdir -p "$CRATE_DOWNLOAD_DIR/203_shell-escape"
wget -c "https://crates.io/api/v1/crates/shell-escape/0.1.4/download" -O "$CRATE_DOWNLOAD_DIR/203_shell-escape/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/203_shell-escape/source"
tar -xf "$CRATE_DOWNLOAD_DIR/203_shell-escape/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/203_shell-escape/source" --strip-components=1

# 204 id=sha1 name=sha1
mkdir -p "$CRATE_DOWNLOAD_DIR/204_sha1"
wget -c "https://crates.io/api/v1/crates/sha1/0.6.0/download" -O "$CRATE_DOWNLOAD_DIR/204_sha1/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/204_sha1/source"
tar -xf "$CRATE_DOWNLOAD_DIR/204_sha1/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/204_sha1/source" --strip-components=1

# 205 id=tokio-executor name=tokio-executor
mkdir -p "$CRATE_DOWNLOAD_DIR/205_tokio-executor"
wget -c "https://crates.io/api/v1/crates/tokio-executor/0.1.5/download" -O "$CRATE_DOWNLOAD_DIR/205_tokio-executor/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/205_tokio-executor/source"
tar -xf "$CRATE_DOWNLOAD_DIR/205_tokio-executor/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/205_tokio-executor/source" --strip-components=1

# 206 id=generic-array name=generic-array
mkdir -p "$CRATE_DOWNLOAD_DIR/206_generic-array"
wget -c "https://crates.io/api/v1/crates/generic-array/0.12.0/download" -O "$CRATE_DOWNLOAD_DIR/206_generic-array/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/206_generic-array/source"
tar -xf "$CRATE_DOWNLOAD_DIR/206_generic-array/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/206_generic-array/source" --strip-components=1

# 207 id=unsafe-any name=unsafe-any
mkdir -p "$CRATE_DOWNLOAD_DIR/207_unsafe-any"
wget -c "https://crates.io/api/v1/crates/unsafe-any/0.4.2/download" -O "$CRATE_DOWNLOAD_DIR/207_unsafe-any/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/207_unsafe-any/source"
tar -xf "$CRATE_DOWNLOAD_DIR/207_unsafe-any/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/207_unsafe-any/source" --strip-components=1

# 208 id=xattr name=xattr
mkdir -p "$CRATE_DOWNLOAD_DIR/208_xattr"
wget -c "https://crates.io/api/v1/crates/xattr/0.2.2/download" -O "$CRATE_DOWNLOAD_DIR/208_xattr/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/208_xattr/source"
tar -xf "$CRATE_DOWNLOAD_DIR/208_xattr/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/208_xattr/source" --strip-components=1

# 209 id=fixedbitset name=fixedbitset
mkdir -p "$CRATE_DOWNLOAD_DIR/209_fixedbitset"
wget -c "https://crates.io/api/v1/crates/fixedbitset/0.1.9/download" -O "$CRATE_DOWNLOAD_DIR/209_fixedbitset/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/209_fixedbitset/source"
tar -xf "$CRATE_DOWNLOAD_DIR/209_fixedbitset/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/209_fixedbitset/source" --strip-components=1

# 210 id=typemap name=typemap
mkdir -p "$CRATE_DOWNLOAD_DIR/210_typemap"
wget -c "https://crates.io/api/v1/crates/typemap/0.3.3/download" -O "$CRATE_DOWNLOAD_DIR/210_typemap/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/210_typemap/source"
tar -xf "$CRATE_DOWNLOAD_DIR/210_typemap/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/210_typemap/source" --strip-components=1

# 211 id=open name=open
mkdir -p "$CRATE_DOWNLOAD_DIR/211_open"
wget -c "https://crates.io/api/v1/crates/open/1.2.2/download" -O "$CRATE_DOWNLOAD_DIR/211_open/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/211_open/source"
tar -xf "$CRATE_DOWNLOAD_DIR/211_open/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/211_open/source" --strip-components=1

# 212 id=petgraph name=petgraph
mkdir -p "$CRATE_DOWNLOAD_DIR/212_petgraph"
wget -c "https://crates.io/api/v1/crates/petgraph/0.4.13/download" -O "$CRATE_DOWNLOAD_DIR/212_petgraph/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/212_petgraph/source"
tar -xf "$CRATE_DOWNLOAD_DIR/212_petgraph/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/212_petgraph/source" --strip-components=1

# 213 id=openssl-sys-extras name=openssl-sys-extras
mkdir -p "$CRATE_DOWNLOAD_DIR/213_openssl-sys-extras"
wget -c "https://crates.io/api/v1/crates/openssl-sys-extras/0.7.14/download" -O "$CRATE_DOWNLOAD_DIR/213_openssl-sys-extras/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/213_openssl-sys-extras/source"
tar -xf "$CRATE_DOWNLOAD_DIR/213_openssl-sys-extras/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/213_openssl-sys-extras/source" --strip-components=1

# 214 id=crc name=crc
mkdir -p "$CRATE_DOWNLOAD_DIR/214_crc"
wget -c "https://crates.io/api/v1/crates/crc/1.8.1/download" -O "$CRATE_DOWNLOAD_DIR/214_crc/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/214_crc/source"
tar -xf "$CRATE_DOWNLOAD_DIR/214_crc/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/214_crc/source" --strip-components=1

# 215 id=reqwest name=reqwest
mkdir -p "$CRATE_DOWNLOAD_DIR/215_reqwest"
wget -c "https://crates.io/api/v1/crates/reqwest/0.9.3/download" -O "$CRATE_DOWNLOAD_DIR/215_reqwest/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/215_reqwest/source"
tar -xf "$CRATE_DOWNLOAD_DIR/215_reqwest/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/215_reqwest/source" --strip-components=1

# 216 id=bincode name=bincode
mkdir -p "$CRATE_DOWNLOAD_DIR/216_bincode"
wget -c "https://crates.io/api/v1/crates/bincode/1.0.1/download" -O "$CRATE_DOWNLOAD_DIR/216_bincode/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/216_bincode/source"
tar -xf "$CRATE_DOWNLOAD_DIR/216_bincode/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/216_bincode/source" --strip-components=1

# 217 id=quine-mc_cluskey name=quine-mc_cluskey
mkdir -p "$CRATE_DOWNLOAD_DIR/217_quine-mc_cluskey"
wget -c "https://crates.io/api/v1/crates/quine-mc_cluskey/0.2.4/download" -O "$CRATE_DOWNLOAD_DIR/217_quine-mc_cluskey/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/217_quine-mc_cluskey/source"
tar -xf "$CRATE_DOWNLOAD_DIR/217_quine-mc_cluskey/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/217_quine-mc_cluskey/source" --strip-components=1

# 218 id=relay name=relay
mkdir -p "$CRATE_DOWNLOAD_DIR/218_relay"
wget -c "https://crates.io/api/v1/crates/relay/0.1.1/download" -O "$CRATE_DOWNLOAD_DIR/218_relay/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/218_relay/source"
tar -xf "$CRATE_DOWNLOAD_DIR/218_relay/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/218_relay/source" --strip-components=1

# 219 id=scoped_threadpool name=scoped_threadpool
mkdir -p "$CRATE_DOWNLOAD_DIR/219_scoped_threadpool"
wget -c "https://crates.io/api/v1/crates/scoped_threadpool/0.1.9/download" -O "$CRATE_DOWNLOAD_DIR/219_scoped_threadpool/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/219_scoped_threadpool/source"
tar -xf "$CRATE_DOWNLOAD_DIR/219_scoped_threadpool/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/219_scoped_threadpool/source" --strip-components=1

# 220 id=encoding name=encoding
mkdir -p "$CRATE_DOWNLOAD_DIR/220_encoding"
wget -c "https://crates.io/api/v1/crates/encoding/0.2.33/download" -O "$CRATE_DOWNLOAD_DIR/220_encoding/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/220_encoding/source"
tar -xf "$CRATE_DOWNLOAD_DIR/220_encoding/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/220_encoding/source" --strip-components=1

# 221 id=antidote name=antidote
mkdir -p "$CRATE_DOWNLOAD_DIR/221_antidote"
wget -c "https://crates.io/api/v1/crates/antidote/1.0.0/download" -O "$CRATE_DOWNLOAD_DIR/221_antidote/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/221_antidote/source"
tar -xf "$CRATE_DOWNLOAD_DIR/221_antidote/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/221_antidote/source" --strip-components=1

# 222 id=jobserver name=jobserver
mkdir -p "$CRATE_DOWNLOAD_DIR/222_jobserver"
wget -c "https://crates.io/api/v1/crates/jobserver/0.1.11/download" -O "$CRATE_DOWNLOAD_DIR/222_jobserver/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/222_jobserver/source"
tar -xf "$CRATE_DOWNLOAD_DIR/222_jobserver/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/222_jobserver/source" --strip-components=1

# 223 id=encoding_index_tests name=encoding_index_tests
mkdir -p "$CRATE_DOWNLOAD_DIR/223_encoding_index_tests"
wget -c "https://crates.io/api/v1/crates/encoding_index_tests/0.1.4/download" -O "$CRATE_DOWNLOAD_DIR/223_encoding_index_tests/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/223_encoding_index_tests/source"
tar -xf "$CRATE_DOWNLOAD_DIR/223_encoding_index_tests/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/223_encoding_index_tests/source" --strip-components=1

# 224 id=aster name=aster
mkdir -p "$CRATE_DOWNLOAD_DIR/224_aster"
wget -c "https://crates.io/api/v1/crates/aster/0.41.0/download" -O "$CRATE_DOWNLOAD_DIR/224_aster/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/224_aster/source"
tar -xf "$CRATE_DOWNLOAD_DIR/224_aster/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/224_aster/source" --strip-components=1

# 225 id=termion name=termion
mkdir -p "$CRATE_DOWNLOAD_DIR/225_termion"
wget -c "https://crates.io/api/v1/crates/termion/1.5.1/download" -O "$CRATE_DOWNLOAD_DIR/225_termion/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/225_termion/source"
tar -xf "$CRATE_DOWNLOAD_DIR/225_termion/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/225_termion/source" --strip-components=1

# 226 id=encoding-index-korean name=encoding-index-korean
mkdir -p "$CRATE_DOWNLOAD_DIR/226_encoding-index-korean"
wget -c "https://crates.io/api/v1/crates/encoding-index-korean/1.20141219.5/download" -O "$CRATE_DOWNLOAD_DIR/226_encoding-index-korean/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/226_encoding-index-korean/source"
tar -xf "$CRATE_DOWNLOAD_DIR/226_encoding-index-korean/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/226_encoding-index-korean/source" --strip-components=1

# 227 id=winapi-x86_64-pc-windows-gnu name=winapi-x86_64-pc-windows-gnu
mkdir -p "$CRATE_DOWNLOAD_DIR/227_winapi-x86_64-pc-windows-gnu"
wget -c "https://crates.io/api/v1/crates/winapi-x86_64-pc-windows-gnu/0.4.0/download" -O "$CRATE_DOWNLOAD_DIR/227_winapi-x86_64-pc-windows-gnu/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/227_winapi-x86_64-pc-windows-gnu/source"
tar -xf "$CRATE_DOWNLOAD_DIR/227_winapi-x86_64-pc-windows-gnu/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/227_winapi-x86_64-pc-windows-gnu/source" --strip-components=1

# 228 id=encoding-index-japanese name=encoding-index-japanese
mkdir -p "$CRATE_DOWNLOAD_DIR/228_encoding-index-japanese"
wget -c "https://crates.io/api/v1/crates/encoding-index-japanese/1.20141219.5/download" -O "$CRATE_DOWNLOAD_DIR/228_encoding-index-japanese/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/228_encoding-index-japanese/source"
tar -xf "$CRATE_DOWNLOAD_DIR/228_encoding-index-japanese/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/228_encoding-index-japanese/source" --strip-components=1

# 229 id=encoding-index-tradchinese name=encoding-index-tradchinese
mkdir -p "$CRATE_DOWNLOAD_DIR/229_encoding-index-tradchinese"
wget -c "https://crates.io/api/v1/crates/encoding-index-tradchinese/1.20141219.5/download" -O "$CRATE_DOWNLOAD_DIR/229_encoding-index-tradchinese/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/229_encoding-index-tradchinese/source"
tar -xf "$CRATE_DOWNLOAD_DIR/229_encoding-index-tradchinese/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/229_encoding-index-tradchinese/source" --strip-components=1

# 230 id=encoding-index-simpchinese name=encoding-index-simpchinese
mkdir -p "$CRATE_DOWNLOAD_DIR/230_encoding-index-simpchinese"
wget -c "https://crates.io/api/v1/crates/encoding-index-simpchinese/1.20141219.5/download" -O "$CRATE_DOWNLOAD_DIR/230_encoding-index-simpchinese/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/230_encoding-index-simpchinese/source"
tar -xf "$CRATE_DOWNLOAD_DIR/230_encoding-index-simpchinese/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/230_encoding-index-simpchinese/source" --strip-components=1

# 231 id=encoding-index-singlebyte name=encoding-index-singlebyte
mkdir -p "$CRATE_DOWNLOAD_DIR/231_encoding-index-singlebyte"
wget -c "https://crates.io/api/v1/crates/encoding-index-singlebyte/1.20141219.5/download" -O "$CRATE_DOWNLOAD_DIR/231_encoding-index-singlebyte/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/231_encoding-index-singlebyte/source"
tar -xf "$CRATE_DOWNLOAD_DIR/231_encoding-index-singlebyte/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/231_encoding-index-singlebyte/source" --strip-components=1

# 232 id=tokio-udp name=tokio-udp
mkdir -p "$CRATE_DOWNLOAD_DIR/232_tokio-udp"
wget -c "https://crates.io/api/v1/crates/tokio-udp/0.1.2/download" -O "$CRATE_DOWNLOAD_DIR/232_tokio-udp/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/232_tokio-udp/source"
tar -xf "$CRATE_DOWNLOAD_DIR/232_tokio-udp/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/232_tokio-udp/source" --strip-components=1

# 233 id=tokio-tcp name=tokio-tcp
mkdir -p "$CRATE_DOWNLOAD_DIR/233_tokio-tcp"
wget -c "https://crates.io/api/v1/crates/tokio-tcp/0.1.2/download" -O "$CRATE_DOWNLOAD_DIR/233_tokio-tcp/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/233_tokio-tcp/source"
tar -xf "$CRATE_DOWNLOAD_DIR/233_tokio-tcp/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/233_tokio-tcp/source" --strip-components=1

# 234 id=png name=png
mkdir -p "$CRATE_DOWNLOAD_DIR/234_png"
wget -c "https://crates.io/api/v1/crates/png/0.13.1/download" -O "$CRATE_DOWNLOAD_DIR/234_png/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/234_png/source"
tar -xf "$CRATE_DOWNLOAD_DIR/234_png/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/234_png/source" --strip-components=1

# 235 id=odds name=odds
mkdir -p "$CRATE_DOWNLOAD_DIR/235_odds"
wget -c "https://crates.io/api/v1/crates/odds/0.3.1/download" -O "$CRATE_DOWNLOAD_DIR/235_odds/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/235_odds/source"
tar -xf "$CRATE_DOWNLOAD_DIR/235_odds/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/235_odds/source" --strip-components=1

# 236 id=typenum name=typenum
mkdir -p "$CRATE_DOWNLOAD_DIR/236_typenum"
wget -c "https://crates.io/api/v1/crates/typenum/1.10.0/download" -O "$CRATE_DOWNLOAD_DIR/236_typenum/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/236_typenum/source"
tar -xf "$CRATE_DOWNLOAD_DIR/236_typenum/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/236_typenum/source" --strip-components=1

# 237 id=isatty name=isatty
mkdir -p "$CRATE_DOWNLOAD_DIR/237_isatty"
wget -c "https://crates.io/api/v1/crates/isatty/0.2.0/download" -O "$CRATE_DOWNLOAD_DIR/237_isatty/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/237_isatty/source"
tar -xf "$CRATE_DOWNLOAD_DIR/237_isatty/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/237_isatty/source" --strip-components=1

# 238 id=winapi-i686-pc-windows-gnu name=winapi-i686-pc-windows-gnu
mkdir -p "$CRATE_DOWNLOAD_DIR/238_winapi-i686-pc-windows-gnu"
wget -c "https://crates.io/api/v1/crates/winapi-i686-pc-windows-gnu/0.4.0/download" -O "$CRATE_DOWNLOAD_DIR/238_winapi-i686-pc-windows-gnu/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/238_winapi-i686-pc-windows-gnu/source"
tar -xf "$CRATE_DOWNLOAD_DIR/238_winapi-i686-pc-windows-gnu/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/238_winapi-i686-pc-windows-gnu/source" --strip-components=1

# 239 id=string_cache name=string_cache
mkdir -p "$CRATE_DOWNLOAD_DIR/239_string_cache"
wget -c "https://crates.io/api/v1/crates/string_cache/0.7.3/download" -O "$CRATE_DOWNLOAD_DIR/239_string_cache/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/239_string_cache/source"
tar -xf "$CRATE_DOWNLOAD_DIR/239_string_cache/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/239_string_cache/source" --strip-components=1

# 240 id=quasi name=quasi
mkdir -p "$CRATE_DOWNLOAD_DIR/240_quasi"
wget -c "https://crates.io/api/v1/crates/quasi/0.32.0/download" -O "$CRATE_DOWNLOAD_DIR/240_quasi/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/240_quasi/source"
tar -xf "$CRATE_DOWNLOAD_DIR/240_quasi/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/240_quasi/source" --strip-components=1

# 241 id=image name=image
mkdir -p "$CRATE_DOWNLOAD_DIR/241_image"
wget -c "https://crates.io/api/v1/crates/image/0.20.0/download" -O "$CRATE_DOWNLOAD_DIR/241_image/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/241_image/source"
tar -xf "$CRATE_DOWNLOAD_DIR/241_image/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/241_image/source" --strip-components=1

# 242 id=quasi_codegen name=quasi_codegen
mkdir -p "$CRATE_DOWNLOAD_DIR/242_quasi_codegen"
wget -c "https://crates.io/api/v1/crates/quasi_codegen/0.32.0/download" -O "$CRATE_DOWNLOAD_DIR/242_quasi_codegen/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/242_quasi_codegen/source"
tar -xf "$CRATE_DOWNLOAD_DIR/242_quasi_codegen/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/242_quasi_codegen/source" --strip-components=1

# 243 id=tokio-tls name=tokio-tls
mkdir -p "$CRATE_DOWNLOAD_DIR/243_tokio-tls"
wget -c "https://crates.io/api/v1/crates/tokio-tls/0.2.0/download" -O "$CRATE_DOWNLOAD_DIR/243_tokio-tls/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/243_tokio-tls/source"
tar -xf "$CRATE_DOWNLOAD_DIR/243_tokio-tls/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/243_tokio-tls/source" --strip-components=1

# 244 id=bit-vec name=bit-vec
mkdir -p "$CRATE_DOWNLOAD_DIR/244_bit-vec"
wget -c "https://crates.io/api/v1/crates/bit-vec/0.5.0/download" -O "$CRATE_DOWNLOAD_DIR/244_bit-vec/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/244_bit-vec/source"
tar -xf "$CRATE_DOWNLOAD_DIR/244_bit-vec/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/244_bit-vec/source" --strip-components=1

# 245 id=hyper-tls name=hyper-tls
mkdir -p "$CRATE_DOWNLOAD_DIR/245_hyper-tls"
wget -c "https://crates.io/api/v1/crates/hyper-tls/0.3.1/download" -O "$CRATE_DOWNLOAD_DIR/245_hyper-tls/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/245_hyper-tls/source"
tar -xf "$CRATE_DOWNLOAD_DIR/245_hyper-tls/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/245_hyper-tls/source" --strip-components=1

# 246 id=home name=home
mkdir -p "$CRATE_DOWNLOAD_DIR/246_home"
wget -c "https://crates.io/api/v1/crates/home/0.3.3/download" -O "$CRATE_DOWNLOAD_DIR/246_home/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/246_home/source"
tar -xf "$CRATE_DOWNLOAD_DIR/246_home/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/246_home/source" --strip-components=1

# 247 id=mdbook name=mdbook
mkdir -p "$CRATE_DOWNLOAD_DIR/247_mdbook"
wget -c "https://crates.io/api/v1/crates/mdbook/0.2.2/download" -O "$CRATE_DOWNLOAD_DIR/247_mdbook/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/247_mdbook/source"
tar -xf "$CRATE_DOWNLOAD_DIR/247_mdbook/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/247_mdbook/source" --strip-components=1

# 248 id=ring name=ring
mkdir -p "$CRATE_DOWNLOAD_DIR/248_ring"
wget -c "https://crates.io/api/v1/crates/ring/0.13.2/download" -O "$CRATE_DOWNLOAD_DIR/248_ring/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/248_ring/source"
tar -xf "$CRATE_DOWNLOAD_DIR/248_ring/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/248_ring/source" --strip-components=1

# 249 id=libloading name=libloading
mkdir -p "$CRATE_DOWNLOAD_DIR/249_libloading"
wget -c "https://crates.io/api/v1/crates/libloading/0.5.0/download" -O "$CRATE_DOWNLOAD_DIR/249_libloading/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/249_libloading/source"
tar -xf "$CRATE_DOWNLOAD_DIR/249_libloading/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/249_libloading/source" --strip-components=1

# 250 id=redox_termios name=redox_termios
mkdir -p "$CRATE_DOWNLOAD_DIR/250_redox_termios"
wget -c "https://crates.io/api/v1/crates/redox_termios/0.1.1/download" -O "$CRATE_DOWNLOAD_DIR/250_redox_termios/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/250_redox_termios/source"
tar -xf "$CRATE_DOWNLOAD_DIR/250_redox_termios/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/250_redox_termios/source" --strip-components=1

# 251 id=shared_library name=shared_library
mkdir -p "$CRATE_DOWNLOAD_DIR/251_shared_library"
wget -c "https://crates.io/api/v1/crates/shared_library/0.1.9/download" -O "$CRATE_DOWNLOAD_DIR/251_shared_library/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/251_shared_library/source"
tar -xf "$CRATE_DOWNLOAD_DIR/251_shared_library/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/251_shared_library/source" --strip-components=1

# 252 id=rls-data name=rls-data
mkdir -p "$CRATE_DOWNLOAD_DIR/252_rls-data"
wget -c "https://crates.io/api/v1/crates/rls-data/0.18.1/download" -O "$CRATE_DOWNLOAD_DIR/252_rls-data/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/252_rls-data/source"
tar -xf "$CRATE_DOWNLOAD_DIR/252_rls-data/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/252_rls-data/source" --strip-components=1

# 253 id=inflate name=inflate
mkdir -p "$CRATE_DOWNLOAD_DIR/253_inflate"
wget -c "https://crates.io/api/v1/crates/inflate/0.4.3/download" -O "$CRATE_DOWNLOAD_DIR/253_inflate/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/253_inflate/source"
tar -xf "$CRATE_DOWNLOAD_DIR/253_inflate/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/253_inflate/source" --strip-components=1

# 254 id=schannel name=schannel
mkdir -p "$CRATE_DOWNLOAD_DIR/254_schannel"
wget -c "https://crates.io/api/v1/crates/schannel/0.1.14/download" -O "$CRATE_DOWNLOAD_DIR/254_schannel/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/254_schannel/source"
tar -xf "$CRATE_DOWNLOAD_DIR/254_schannel/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/254_schannel/source" --strip-components=1

# 255 id=html5ever name=html5ever
mkdir -p "$CRATE_DOWNLOAD_DIR/255_html5ever"
wget -c "https://crates.io/api/v1/crates/html5ever/0.22.3/download" -O "$CRATE_DOWNLOAD_DIR/255_html5ever/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/255_html5ever/source"
tar -xf "$CRATE_DOWNLOAD_DIR/255_html5ever/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/255_html5ever/source" --strip-components=1

# 256 id=libflate name=libflate
mkdir -p "$CRATE_DOWNLOAD_DIR/256_libflate"
wget -c "https://crates.io/api/v1/crates/libflate/0.1.18/download" -O "$CRATE_DOWNLOAD_DIR/256_libflate/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/256_libflate/source"
tar -xf "$CRATE_DOWNLOAD_DIR/256_libflate/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/256_libflate/source" --strip-components=1

# 257 id=build_const name=build_const
mkdir -p "$CRATE_DOWNLOAD_DIR/257_build_const"
wget -c "https://crates.io/api/v1/crates/build_const/0.2.1/download" -O "$CRATE_DOWNLOAD_DIR/257_build_const/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/257_build_const/source"
tar -xf "$CRATE_DOWNLOAD_DIR/257_build_const/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/257_build_const/source" --strip-components=1

# 258 id=gif name=gif
mkdir -p "$CRATE_DOWNLOAD_DIR/258_gif"
wget -c "https://crates.io/api/v1/crates/gif/0.10.1/download" -O "$CRATE_DOWNLOAD_DIR/258_gif/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/258_gif/source"
tar -xf "$CRATE_DOWNLOAD_DIR/258_gif/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/258_gif/source" --strip-components=1

# 259 id=derive-new name=derive-new
mkdir -p "$CRATE_DOWNLOAD_DIR/259_derive-new"
wget -c "https://crates.io/api/v1/crates/derive-new/0.5.5/download" -O "$CRATE_DOWNLOAD_DIR/259_derive-new/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/259_derive-new/source"
tar -xf "$CRATE_DOWNLOAD_DIR/259_derive-new/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/259_derive-new/source" --strip-components=1

# 260 id=url_serde name=url_serde
mkdir -p "$CRATE_DOWNLOAD_DIR/260_url_serde"
wget -c "https://crates.io/api/v1/crates/url_serde/0.2.0/download" -O "$CRATE_DOWNLOAD_DIR/260_url_serde/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/260_url_serde/source"
tar -xf "$CRATE_DOWNLOAD_DIR/260_url_serde/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/260_url_serde/source" --strip-components=1

# 261 id=tendril name=tendril
mkdir -p "$CRATE_DOWNLOAD_DIR/261_tendril"
wget -c "https://crates.io/api/v1/crates/tendril/0.4.0/download" -O "$CRATE_DOWNLOAD_DIR/261_tendril/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/261_tendril/source"
tar -xf "$CRATE_DOWNLOAD_DIR/261_tendril/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/261_tendril/source" --strip-components=1

# 262 id=mac name=mac
mkdir -p "$CRATE_DOWNLOAD_DIR/262_mac"
wget -c "https://crates.io/api/v1/crates/mac/0.1.1/download" -O "$CRATE_DOWNLOAD_DIR/262_mac/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/262_mac/source"
tar -xf "$CRATE_DOWNLOAD_DIR/262_mac/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/262_mac/source" --strip-components=1

# 263 id=utf-8 name=utf-8
mkdir -p "$CRATE_DOWNLOAD_DIR/263_utf-8"
wget -c "https://crates.io/api/v1/crates/utf-8/0.7.4/download" -O "$CRATE_DOWNLOAD_DIR/263_utf-8/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/263_utf-8/source"
tar -xf "$CRATE_DOWNLOAD_DIR/263_utf-8/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/263_utf-8/source" --strip-components=1

# 264 id=futf name=futf
mkdir -p "$CRATE_DOWNLOAD_DIR/264_futf"
wget -c "https://crates.io/api/v1/crates/futf/0.1.4/download" -O "$CRATE_DOWNLOAD_DIR/264_futf/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/264_futf/source"
tar -xf "$CRATE_DOWNLOAD_DIR/264_futf/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/264_futf/source" --strip-components=1

# 265 id=modifier name=modifier
mkdir -p "$CRATE_DOWNLOAD_DIR/265_modifier"
wget -c "https://crates.io/api/v1/crates/modifier/0.1.0/download" -O "$CRATE_DOWNLOAD_DIR/265_modifier/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/265_modifier/source"
tar -xf "$CRATE_DOWNLOAD_DIR/265_modifier/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/265_modifier/source" --strip-components=1

# 266 id=plugin name=plugin
mkdir -p "$CRATE_DOWNLOAD_DIR/266_plugin"
wget -c "https://crates.io/api/v1/crates/plugin/0.2.6/download" -O "$CRATE_DOWNLOAD_DIR/266_plugin/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/266_plugin/source"
tar -xf "$CRATE_DOWNLOAD_DIR/266_plugin/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/266_plugin/source" --strip-components=1

# 267 id=pnacl-build-helper name=pnacl-build-helper
mkdir -p "$CRATE_DOWNLOAD_DIR/267_pnacl-build-helper"
wget -c "https://crates.io/api/v1/crates/pnacl-build-helper/1.4.11/download" -O "$CRATE_DOWNLOAD_DIR/267_pnacl-build-helper/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/267_pnacl-build-helper/source"
tar -xf "$CRATE_DOWNLOAD_DIR/267_pnacl-build-helper/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/267_pnacl-build-helper/source" --strip-components=1

# 268 id=quickcheck name=quickcheck
mkdir -p "$CRATE_DOWNLOAD_DIR/268_quickcheck"
wget -c "https://crates.io/api/v1/crates/quickcheck/0.7.1/download" -O "$CRATE_DOWNLOAD_DIR/268_quickcheck/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/268_quickcheck/source"
tar -xf "$CRATE_DOWNLOAD_DIR/268_quickcheck/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/268_quickcheck/source" --strip-components=1

# 269 id=bit-set name=bit-set
mkdir -p "$CRATE_DOWNLOAD_DIR/269_bit-set"
wget -c "https://crates.io/api/v1/crates/bit-set/0.5.0/download" -O "$CRATE_DOWNLOAD_DIR/269_bit-set/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/269_bit-set/source"
tar -xf "$CRATE_DOWNLOAD_DIR/269_bit-set/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/269_bit-set/source" --strip-components=1

# 270 id=rls-span name=rls-span
mkdir -p "$CRATE_DOWNLOAD_DIR/270_rls-span"
wget -c "https://crates.io/api/v1/crates/rls-span/0.4.0/download" -O "$CRATE_DOWNLOAD_DIR/270_rls-span/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/270_rls-span/source"
tar -xf "$CRATE_DOWNLOAD_DIR/270_rls-span/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/270_rls-span/source" --strip-components=1

# 271 id=lzw name=lzw
mkdir -p "$CRATE_DOWNLOAD_DIR/271_lzw"
wget -c "https://crates.io/api/v1/crates/lzw/0.10.0/download" -O "$CRATE_DOWNLOAD_DIR/271_lzw/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/271_lzw/source"
tar -xf "$CRATE_DOWNLOAD_DIR/271_lzw/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/271_lzw/source" --strip-components=1

# 272 id=libressl-pnacl-sys name=libressl-pnacl-sys
mkdir -p "$CRATE_DOWNLOAD_DIR/272_libressl-pnacl-sys"
wget -c "https://crates.io/api/v1/crates/libressl-pnacl-sys/2.1.6/download" -O "$CRATE_DOWNLOAD_DIR/272_libressl-pnacl-sys/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/272_libressl-pnacl-sys/source"
tar -xf "$CRATE_DOWNLOAD_DIR/272_libressl-pnacl-sys/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/272_libressl-pnacl-sys/source" --strip-components=1

# 273 id=jsonrpc-core name=jsonrpc-core
mkdir -p "$CRATE_DOWNLOAD_DIR/273_jsonrpc-core"
wget -c "https://crates.io/api/v1/crates/jsonrpc-core/8.0.1/download" -O "$CRATE_DOWNLOAD_DIR/273_jsonrpc-core/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/273_jsonrpc-core/source"
tar -xf "$CRATE_DOWNLOAD_DIR/273_jsonrpc-core/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/273_jsonrpc-core/source" --strip-components=1

# 274 id=digest name=digest
mkdir -p "$CRATE_DOWNLOAD_DIR/274_digest"
wget -c "https://crates.io/api/v1/crates/digest/0.8.0/download" -O "$CRATE_DOWNLOAD_DIR/274_digest/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/274_digest/source"
tar -xf "$CRATE_DOWNLOAD_DIR/274_digest/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/274_digest/source" --strip-components=1

# 275 id=color_quant name=color_quant
mkdir -p "$CRATE_DOWNLOAD_DIR/275_color_quant"
wget -c "https://crates.io/api/v1/crates/color_quant/1.0.1/download" -O "$CRATE_DOWNLOAD_DIR/275_color_quant/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/275_color_quant/source"
tar -xf "$CRATE_DOWNLOAD_DIR/275_color_quant/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/275_color_quant/source" --strip-components=1

# 276 id=lzma-sys name=lzma-sys
mkdir -p "$CRATE_DOWNLOAD_DIR/276_lzma-sys"
wget -c "https://crates.io/api/v1/crates/lzma-sys/0.1.11/download" -O "$CRATE_DOWNLOAD_DIR/276_lzma-sys/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/276_lzma-sys/source"
tar -xf "$CRATE_DOWNLOAD_DIR/276_lzma-sys/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/276_lzma-sys/source" --strip-components=1

# 277 id=iron name=iron
mkdir -p "$CRATE_DOWNLOAD_DIR/277_iron"
wget -c "https://crates.io/api/v1/crates/iron/0.6.0/download" -O "$CRATE_DOWNLOAD_DIR/277_iron/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/277_iron/source"
tar -xf "$CRATE_DOWNLOAD_DIR/277_iron/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/277_iron/source" --strip-components=1

# 278 id=tokio-fs name=tokio-fs
mkdir -p "$CRATE_DOWNLOAD_DIR/278_tokio-fs"
wget -c "https://crates.io/api/v1/crates/tokio-fs/0.1.3/download" -O "$CRATE_DOWNLOAD_DIR/278_tokio-fs/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/278_tokio-fs/source"
tar -xf "$CRATE_DOWNLOAD_DIR/278_tokio-fs/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/278_tokio-fs/source" --strip-components=1

# 279 id=xz2 name=xz2
mkdir -p "$CRATE_DOWNLOAD_DIR/279_xz2"
wget -c "https://crates.io/api/v1/crates/xz2/0.1.6/download" -O "$CRATE_DOWNLOAD_DIR/279_xz2/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/279_xz2/source"
tar -xf "$CRATE_DOWNLOAD_DIR/279_xz2/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/279_xz2/source" --strip-components=1

# 280 id=shlex name=shlex
mkdir -p "$CRATE_DOWNLOAD_DIR/280_shlex"
wget -c "https://crates.io/api/v1/crates/shlex/0.1.1/download" -O "$CRATE_DOWNLOAD_DIR/280_shlex/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/280_shlex/source"
tar -xf "$CRATE_DOWNLOAD_DIR/280_shlex/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/280_shlex/source" --strip-components=1

# 281 id=coco name=coco
mkdir -p "$CRATE_DOWNLOAD_DIR/281_coco"
wget -c "https://crates.io/api/v1/crates/coco/0.3.4/download" -O "$CRATE_DOWNLOAD_DIR/281_coco/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/281_coco/source"
tar -xf "$CRATE_DOWNLOAD_DIR/281_coco/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/281_coco/source" --strip-components=1

# 282 id=string_cache_shared name=string_cache_shared
mkdir -p "$CRATE_DOWNLOAD_DIR/282_string_cache_shared"
wget -c "https://crates.io/api/v1/crates/string_cache_shared/0.3.0/download" -O "$CRATE_DOWNLOAD_DIR/282_string_cache_shared/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/282_string_cache_shared/source"
tar -xf "$CRATE_DOWNLOAD_DIR/282_string_cache_shared/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/282_string_cache_shared/source" --strip-components=1

# 283 id=languageserver-types name=languageserver-types
mkdir -p "$CRATE_DOWNLOAD_DIR/283_languageserver-types"
wget -c "https://crates.io/api/v1/crates/languageserver-types/0.51.0/download" -O "$CRATE_DOWNLOAD_DIR/283_languageserver-types/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/283_languageserver-types/source"
tar -xf "$CRATE_DOWNLOAD_DIR/283_languageserver-types/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/283_languageserver-types/source" --strip-components=1

# 284 id=string_cache_codegen name=string_cache_codegen
mkdir -p "$CRATE_DOWNLOAD_DIR/284_string_cache_codegen"
wget -c "https://crates.io/api/v1/crates/string_cache_codegen/0.4.2/download" -O "$CRATE_DOWNLOAD_DIR/284_string_cache_codegen/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/284_string_cache_codegen/source"
tar -xf "$CRATE_DOWNLOAD_DIR/284_string_cache_codegen/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/284_string_cache_codegen/source" --strip-components=1

# 285 id=compiletest_rs name=compiletest_rs
mkdir -p "$CRATE_DOWNLOAD_DIR/285_compiletest_rs"
wget -c "https://crates.io/api/v1/crates/compiletest_rs/0.3.14/download" -O "$CRATE_DOWNLOAD_DIR/285_compiletest_rs/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/285_compiletest_rs/source"
tar -xf "$CRATE_DOWNLOAD_DIR/285_compiletest_rs/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/285_compiletest_rs/source" --strip-components=1

# 286 id=ryu name=ryu
mkdir -p "$CRATE_DOWNLOAD_DIR/286_ryu"
wget -c "https://crates.io/api/v1/crates/ryu/0.2.6/download" -O "$CRATE_DOWNLOAD_DIR/286_ryu/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/286_ryu/source"
tar -xf "$CRATE_DOWNLOAD_DIR/286_ryu/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/286_ryu/source" --strip-components=1

# 287 id=byte-tools name=byte-tools
mkdir -p "$CRATE_DOWNLOAD_DIR/287_byte-tools"
wget -c "https://crates.io/api/v1/crates/byte-tools/0.3.0/download" -O "$CRATE_DOWNLOAD_DIR/287_byte-tools/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/287_byte-tools/source"
tar -xf "$CRATE_DOWNLOAD_DIR/287_byte-tools/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/287_byte-tools/source" --strip-components=1

# 288 id=rls-analysis name=rls-analysis
mkdir -p "$CRATE_DOWNLOAD_DIR/288_rls-analysis"
wget -c "https://crates.io/api/v1/crates/rls-analysis/0.16.1/download" -O "$CRATE_DOWNLOAD_DIR/288_rls-analysis/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/288_rls-analysis/source"
tar -xf "$CRATE_DOWNLOAD_DIR/288_rls-analysis/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/288_rls-analysis/source" --strip-components=1

# 289 id=glutin name=glutin
mkdir -p "$CRATE_DOWNLOAD_DIR/289_glutin"
wget -c "https://crates.io/api/v1/crates/glutin/0.18.0/download" -O "$CRATE_DOWNLOAD_DIR/289_glutin/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/289_glutin/source"
tar -xf "$CRATE_DOWNLOAD_DIR/289_glutin/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/289_glutin/source" --strip-components=1

# 290 id=rls-vfs name=rls-vfs
mkdir -p "$CRATE_DOWNLOAD_DIR/290_rls-vfs"
wget -c "https://crates.io/api/v1/crates/rls-vfs/0.6.0/download" -O "$CRATE_DOWNLOAD_DIR/290_rls-vfs/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/290_rls-vfs/source"
tar -xf "$CRATE_DOWNLOAD_DIR/290_rls-vfs/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/290_rls-vfs/source" --strip-components=1

# 291 id=crypto-hash name=crypto-hash
mkdir -p "$CRATE_DOWNLOAD_DIR/291_crypto-hash"
wget -c "https://crates.io/api/v1/crates/crypto-hash/0.3.1/download" -O "$CRATE_DOWNLOAD_DIR/291_crypto-hash/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/291_crypto-hash/source"
tar -xf "$CRATE_DOWNLOAD_DIR/291_crypto-hash/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/291_crypto-hash/source" --strip-components=1

# 292 id=sha2 name=sha2
mkdir -p "$CRATE_DOWNLOAD_DIR/292_sha2"
wget -c "https://crates.io/api/v1/crates/sha2/0.8.0/download" -O "$CRATE_DOWNLOAD_DIR/292_sha2/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/292_sha2/source"
tar -xf "$CRATE_DOWNLOAD_DIR/292_sha2/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/292_sha2/source" --strip-components=1

# 293 id=clippy name=clippy
mkdir -p "$CRATE_DOWNLOAD_DIR/293_clippy"
wget -c "https://crates.io/api/v1/crates/clippy/0.0.302/download" -O "$CRATE_DOWNLOAD_DIR/293_clippy/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/293_clippy/source"
tar -xf "$CRATE_DOWNLOAD_DIR/293_clippy/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/293_clippy/source" --strip-components=1

# 294 id=precomputed-hash name=precomputed-hash
mkdir -p "$CRATE_DOWNLOAD_DIR/294_precomputed-hash"
wget -c "https://crates.io/api/v1/crates/precomputed-hash/0.1.1/download" -O "$CRATE_DOWNLOAD_DIR/294_precomputed-hash/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/294_precomputed-hash/source"
tar -xf "$CRATE_DOWNLOAD_DIR/294_precomputed-hash/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/294_precomputed-hash/source" --strip-components=1

# 295 id=if_chain name=if_chain
mkdir -p "$CRATE_DOWNLOAD_DIR/295_if_chain"
wget -c "https://crates.io/api/v1/crates/if_chain/0.1.3/download" -O "$CRATE_DOWNLOAD_DIR/295_if_chain/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/295_if_chain/source"
tar -xf "$CRATE_DOWNLOAD_DIR/295_if_chain/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/295_if_chain/source" --strip-components=1

# 296 id=jpeg-decoder name=jpeg-decoder
mkdir -p "$CRATE_DOWNLOAD_DIR/296_jpeg-decoder"
wget -c "https://crates.io/api/v1/crates/jpeg-decoder/0.1.15/download" -O "$CRATE_DOWNLOAD_DIR/296_jpeg-decoder/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/296_jpeg-decoder/source"
tar -xf "$CRATE_DOWNLOAD_DIR/296_jpeg-decoder/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/296_jpeg-decoder/source" --strip-components=1

# 297 id=markup5ever name=markup5ever
mkdir -p "$CRATE_DOWNLOAD_DIR/297_markup5ever"
wget -c "https://crates.io/api/v1/crates/markup5ever/0.7.3/download" -O "$CRATE_DOWNLOAD_DIR/297_markup5ever/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/297_markup5ever/source"
tar -xf "$CRATE_DOWNLOAD_DIR/297_markup5ever/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/297_markup5ever/source" --strip-components=1

# 298 id=conduit-mime-types name=conduit-mime-types
mkdir -p "$CRATE_DOWNLOAD_DIR/298_conduit-mime-types"
wget -c "https://crates.io/api/v1/crates/conduit-mime-types/0.7.3/download" -O "$CRATE_DOWNLOAD_DIR/298_conduit-mime-types/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/298_conduit-mime-types/source"
tar -xf "$CRATE_DOWNLOAD_DIR/298_conduit-mime-types/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/298_conduit-mime-types/source" --strip-components=1

# 299 id=ordered-float name=ordered-float
mkdir -p "$CRATE_DOWNLOAD_DIR/299_ordered-float"
wget -c "https://crates.io/api/v1/crates/ordered-float/1.0.1/download" -O "$CRATE_DOWNLOAD_DIR/299_ordered-float/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/299_ordered-float/source"
tar -xf "$CRATE_DOWNLOAD_DIR/299_ordered-float/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/299_ordered-float/source" --strip-components=1

# 300 id=difference name=difference
mkdir -p "$CRATE_DOWNLOAD_DIR/300_difference"
wget -c "https://crates.io/api/v1/crates/difference/2.0.0/download" -O "$CRATE_DOWNLOAD_DIR/300_difference/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/300_difference/source"
tar -xf "$CRATE_DOWNLOAD_DIR/300_difference/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/300_difference/source" --strip-components=1

# 301 id=debug_unreachable name=debug_unreachable
mkdir -p "$CRATE_DOWNLOAD_DIR/301_debug_unreachable"
wget -c "https://crates.io/api/v1/crates/debug_unreachable/0.1.1/download" -O "$CRATE_DOWNLOAD_DIR/301_debug_unreachable/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/301_debug_unreachable/source"
tar -xf "$CRATE_DOWNLOAD_DIR/301_debug_unreachable/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/301_debug_unreachable/source" --strip-components=1

# 302 id=fake-simd name=fake-simd
mkdir -p "$CRATE_DOWNLOAD_DIR/302_fake-simd"
wget -c "https://crates.io/api/v1/crates/fake-simd/0.1.2/download" -O "$CRATE_DOWNLOAD_DIR/302_fake-simd/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/302_fake-simd/source"
tar -xf "$CRATE_DOWNLOAD_DIR/302_fake-simd/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/302_fake-simd/source" --strip-components=1

# 303 id=mio-uds name=mio-uds
mkdir -p "$CRATE_DOWNLOAD_DIR/303_mio-uds"
wget -c "https://crates.io/api/v1/crates/mio-uds/0.6.7/download" -O "$CRATE_DOWNLOAD_DIR/303_mio-uds/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/303_mio-uds/source"
tar -xf "$CRATE_DOWNLOAD_DIR/303_mio-uds/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/303_mio-uds/source" --strip-components=1

# 304 id=error name=error
mkdir -p "$CRATE_DOWNLOAD_DIR/304_error"
wget -c "https://crates.io/api/v1/crates/error/0.1.9/download" -O "$CRATE_DOWNLOAD_DIR/304_error/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/304_error/source"
tar -xf "$CRATE_DOWNLOAD_DIR/304_error/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/304_error/source" --strip-components=1

# 305 id=json name=json
mkdir -p "$CRATE_DOWNLOAD_DIR/305_json"
wget -c "https://crates.io/api/v1/crates/json/0.11.13/download" -O "$CRATE_DOWNLOAD_DIR/305_json/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/305_json/source"
tar -xf "$CRATE_DOWNLOAD_DIR/305_json/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/305_json/source" --strip-components=1

# 306 id=deflate name=deflate
mkdir -p "$CRATE_DOWNLOAD_DIR/306_deflate"
wget -c "https://crates.io/api/v1/crates/deflate/0.7.19/download" -O "$CRATE_DOWNLOAD_DIR/306_deflate/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/306_deflate/source"
tar -xf "$CRATE_DOWNLOAD_DIR/306_deflate/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/306_deflate/source" --strip-components=1

# 307 id=protobuf name=protobuf
mkdir -p "$CRATE_DOWNLOAD_DIR/307_protobuf"
wget -c "https://crates.io/api/v1/crates/protobuf/2.1.1/download" -O "$CRATE_DOWNLOAD_DIR/307_protobuf/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/307_protobuf/source"
tar -xf "$CRATE_DOWNLOAD_DIR/307_protobuf/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/307_protobuf/source" --strip-components=1

# 308 id=x11-dl name=x11-dl
mkdir -p "$CRATE_DOWNLOAD_DIR/308_x11-dl"
wget -c "https://crates.io/api/v1/crates/x11-dl/2.18.3/download" -O "$CRATE_DOWNLOAD_DIR/308_x11-dl/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/308_x11-dl/source"
tar -xf "$CRATE_DOWNLOAD_DIR/308_x11-dl/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/308_x11-dl/source" --strip-components=1

# 309 id=deque name=deque
mkdir -p "$CRATE_DOWNLOAD_DIR/309_deque"
wget -c "https://crates.io/api/v1/crates/deque/0.3.2/download" -O "$CRATE_DOWNLOAD_DIR/309_deque/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/309_deque/source"
tar -xf "$CRATE_DOWNLOAD_DIR/309_deque/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/309_deque/source" --strip-components=1

# 310 id=typed-arena name=typed-arena
mkdir -p "$CRATE_DOWNLOAD_DIR/310_typed-arena"
wget -c "https://crates.io/api/v1/crates/typed-arena/1.4.1/download" -O "$CRATE_DOWNLOAD_DIR/310_typed-arena/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/310_typed-arena/source"
tar -xf "$CRATE_DOWNLOAD_DIR/310_typed-arena/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/310_typed-arena/source" --strip-components=1

# 311 id=userenv-sys name=userenv-sys
mkdir -p "$CRATE_DOWNLOAD_DIR/311_userenv-sys"
wget -c "https://crates.io/api/v1/crates/userenv-sys/0.2.0/download" -O "$CRATE_DOWNLOAD_DIR/311_userenv-sys/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/311_userenv-sys/source"
tar -xf "$CRATE_DOWNLOAD_DIR/311_userenv-sys/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/311_userenv-sys/source" --strip-components=1

# 312 id=constant_time_eq name=constant_time_eq
mkdir -p "$CRATE_DOWNLOAD_DIR/312_constant_time_eq"
wget -c "https://crates.io/api/v1/crates/constant_time_eq/0.1.3/download" -O "$CRATE_DOWNLOAD_DIR/312_constant_time_eq/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/312_constant_time_eq/source"
tar -xf "$CRATE_DOWNLOAD_DIR/312_constant_time_eq/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/312_constant_time_eq/source" --strip-components=1

# 313 id=heapsize name=heapsize
mkdir -p "$CRATE_DOWNLOAD_DIR/313_heapsize"
wget -c "https://crates.io/api/v1/crates/heapsize/0.4.2/download" -O "$CRATE_DOWNLOAD_DIR/313_heapsize/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/313_heapsize/source"
tar -xf "$CRATE_DOWNLOAD_DIR/313_heapsize/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/313_heapsize/source" --strip-components=1

# 314 id=commoncrypto-sys name=commoncrypto-sys
mkdir -p "$CRATE_DOWNLOAD_DIR/314_commoncrypto-sys"
wget -c "https://crates.io/api/v1/crates/commoncrypto-sys/0.2.0/download" -O "$CRATE_DOWNLOAD_DIR/314_commoncrypto-sys/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/314_commoncrypto-sys/source"
tar -xf "$CRATE_DOWNLOAD_DIR/314_commoncrypto-sys/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/314_commoncrypto-sys/source" --strip-components=1

# 315 id=commoncrypto name=commoncrypto
mkdir -p "$CRATE_DOWNLOAD_DIR/315_commoncrypto"
wget -c "https://crates.io/api/v1/crates/commoncrypto/0.2.0/download" -O "$CRATE_DOWNLOAD_DIR/315_commoncrypto/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/315_commoncrypto/source"
tar -xf "$CRATE_DOWNLOAD_DIR/315_commoncrypto/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/315_commoncrypto/source" --strip-components=1

# 316 id=csv name=csv
mkdir -p "$CRATE_DOWNLOAD_DIR/316_csv"
wget -c "https://crates.io/api/v1/crates/csv/1.0.2/download" -O "$CRATE_DOWNLOAD_DIR/316_csv/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/316_csv/source"
tar -xf "$CRATE_DOWNLOAD_DIR/316_csv/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/316_csv/source" --strip-components=1

# 317 id=lock_api name=lock_api
mkdir -p "$CRATE_DOWNLOAD_DIR/317_lock_api"
wget -c "https://crates.io/api/v1/crates/lock_api/0.1.4/download" -O "$CRATE_DOWNLOAD_DIR/317_lock_api/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/317_lock_api/source"
tar -xf "$CRATE_DOWNLOAD_DIR/317_lock_api/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/317_lock_api/source" --strip-components=1

# 318 id=rls-rustc name=rls-rustc
mkdir -p "$CRATE_DOWNLOAD_DIR/318_rls-rustc"
wget -c "https://crates.io/api/v1/crates/rls-rustc/0.5.0/download" -O "$CRATE_DOWNLOAD_DIR/318_rls-rustc/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/318_rls-rustc/source"
tar -xf "$CRATE_DOWNLOAD_DIR/318_rls-rustc/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/318_rls-rustc/source" --strip-components=1

# 319 id=serde_yaml name=serde_yaml
mkdir -p "$CRATE_DOWNLOAD_DIR/319_serde_yaml"
wget -c "https://crates.io/api/v1/crates/serde_yaml/0.8.6/download" -O "$CRATE_DOWNLOAD_DIR/319_serde_yaml/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/319_serde_yaml/source"
tar -xf "$CRATE_DOWNLOAD_DIR/319_serde_yaml/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/319_serde_yaml/source" --strip-components=1

# 320 id=gleam name=gleam
mkdir -p "$CRATE_DOWNLOAD_DIR/320_gleam"
wget -c "https://crates.io/api/v1/crates/gleam/0.6.4/download" -O "$CRATE_DOWNLOAD_DIR/320_gleam/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/320_gleam/source"
tar -xf "$CRATE_DOWNLOAD_DIR/320_gleam/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/320_gleam/source" --strip-components=1

# 321 id=ascii name=ascii
mkdir -p "$CRATE_DOWNLOAD_DIR/321_ascii"
wget -c "https://crates.io/api/v1/crates/ascii/0.9.1/download" -O "$CRATE_DOWNLOAD_DIR/321_ascii/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/321_ascii/source"
tar -xf "$CRATE_DOWNLOAD_DIR/321_ascii/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/321_ascii/source" --strip-components=1

# 322 id=zip name=zip
mkdir -p "$CRATE_DOWNLOAD_DIR/322_zip"
wget -c "https://crates.io/api/v1/crates/zip/0.4.2/download" -O "$CRATE_DOWNLOAD_DIR/322_zip/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/322_zip/source"
tar -xf "$CRATE_DOWNLOAD_DIR/322_zip/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/322_zip/source" --strip-components=1

# 323 id=rustc-ap-serialize name=rustc-ap-serialize
mkdir -p "$CRATE_DOWNLOAD_DIR/323_rustc-ap-serialize"
wget -c "https://crates.io/api/v1/crates/rustc-ap-serialize/274.0.0/download" -O "$CRATE_DOWNLOAD_DIR/323_rustc-ap-serialize/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/323_rustc-ap-serialize/source"
tar -xf "$CRATE_DOWNLOAD_DIR/323_rustc-ap-serialize/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/323_rustc-ap-serialize/source" --strip-components=1

# 324 id=rustc-ap-syntax_pos name=rustc-ap-syntax_pos
mkdir -p "$CRATE_DOWNLOAD_DIR/324_rustc-ap-syntax_pos"
wget -c "https://crates.io/api/v1/crates/rustc-ap-syntax_pos/274.0.0/download" -O "$CRATE_DOWNLOAD_DIR/324_rustc-ap-syntax_pos/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/324_rustc-ap-syntax_pos/source"
tar -xf "$CRATE_DOWNLOAD_DIR/324_rustc-ap-syntax_pos/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/324_rustc-ap-syntax_pos/source" --strip-components=1

# 325 id=rustc-ap-rustc_data_structures name=rustc-ap-rustc_data_structures
mkdir -p "$CRATE_DOWNLOAD_DIR/325_rustc-ap-rustc_data_structures"
wget -c "https://crates.io/api/v1/crates/rustc-ap-rustc_data_structures/274.0.0/download" -O "$CRATE_DOWNLOAD_DIR/325_rustc-ap-rustc_data_structures/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/325_rustc-ap-rustc_data_structures/source"
tar -xf "$CRATE_DOWNLOAD_DIR/325_rustc-ap-rustc_data_structures/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/325_rustc-ap-rustc_data_structures/source" --strip-components=1

# 326 id=rustc-ap-rustc_cratesio_shim name=rustc-ap-rustc_cratesio_shim
mkdir -p "$CRATE_DOWNLOAD_DIR/326_rustc-ap-rustc_cratesio_shim"
wget -c "https://crates.io/api/v1/crates/rustc-ap-rustc_cratesio_shim/274.0.0/download" -O "$CRATE_DOWNLOAD_DIR/326_rustc-ap-rustc_cratesio_shim/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/326_rustc-ap-rustc_cratesio_shim/source"
tar -xf "$CRATE_DOWNLOAD_DIR/326_rustc-ap-rustc_cratesio_shim/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/326_rustc-ap-rustc_cratesio_shim/source" --strip-components=1

# 327 id=rustc-ap-rustc_errors name=rustc-ap-rustc_errors
mkdir -p "$CRATE_DOWNLOAD_DIR/327_rustc-ap-rustc_errors"
wget -c "https://crates.io/api/v1/crates/rustc-ap-rustc_errors/274.0.0/download" -O "$CRATE_DOWNLOAD_DIR/327_rustc-ap-rustc_errors/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/327_rustc-ap-rustc_errors/source"
tar -xf "$CRATE_DOWNLOAD_DIR/327_rustc-ap-rustc_errors/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/327_rustc-ap-rustc_errors/source" --strip-components=1

# 328 id=rustc-ap-syntax name=rustc-ap-syntax
mkdir -p "$CRATE_DOWNLOAD_DIR/328_rustc-ap-syntax"
wget -c "https://crates.io/api/v1/crates/rustc-ap-syntax/274.0.0/download" -O "$CRATE_DOWNLOAD_DIR/328_rustc-ap-syntax/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/328_rustc-ap-syntax/source"
tar -xf "$CRATE_DOWNLOAD_DIR/328_rustc-ap-syntax/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/328_rustc-ap-syntax/source" --strip-components=1

# 329 id=wayland-client name=wayland-client
mkdir -p "$CRATE_DOWNLOAD_DIR/329_wayland-client"
wget -c "https://crates.io/api/v1/crates/wayland-client/0.21.2/download" -O "$CRATE_DOWNLOAD_DIR/329_wayland-client/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/329_wayland-client/source"
tar -xf "$CRATE_DOWNLOAD_DIR/329_wayland-client/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/329_wayland-client/source" --strip-components=1

# 330 id=encoding_rs name=encoding_rs
mkdir -p "$CRATE_DOWNLOAD_DIR/330_encoding_rs"
wget -c "https://crates.io/api/v1/crates/encoding_rs/0.8.10/download" -O "$CRATE_DOWNLOAD_DIR/330_encoding_rs/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/330_encoding_rs/source"
tar -xf "$CRATE_DOWNLOAD_DIR/330_encoding_rs/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/330_encoding_rs/source" --strip-components=1

# 331 id=tokio-codec name=tokio-codec
mkdir -p "$CRATE_DOWNLOAD_DIR/331_tokio-codec"
wget -c "https://crates.io/api/v1/crates/tokio-codec/0.1.1/download" -O "$CRATE_DOWNLOAD_DIR/331_tokio-codec/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/331_tokio-codec/source"
tar -xf "$CRATE_DOWNLOAD_DIR/331_tokio-codec/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/331_tokio-codec/source" --strip-components=1

# 332 id=maplit name=maplit
mkdir -p "$CRATE_DOWNLOAD_DIR/332_maplit"
wget -c "https://crates.io/api/v1/crates/maplit/1.0.1/download" -O "$CRATE_DOWNLOAD_DIR/332_maplit/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/332_maplit/source"
tar -xf "$CRATE_DOWNLOAD_DIR/332_maplit/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/332_maplit/source" --strip-components=1

# 333 id=podio name=podio
mkdir -p "$CRATE_DOWNLOAD_DIR/333_podio"
wget -c "https://crates.io/api/v1/crates/podio/0.1.6/download" -O "$CRATE_DOWNLOAD_DIR/333_podio/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/333_podio/source"
tar -xf "$CRATE_DOWNLOAD_DIR/333_podio/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/333_podio/source" --strip-components=1

# 334 id=strings name=strings
mkdir -p "$CRATE_DOWNLOAD_DIR/334_strings"
wget -c "https://crates.io/api/v1/crates/strings/0.1.1/download" -O "$CRATE_DOWNLOAD_DIR/334_strings/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/334_strings/source"
tar -xf "$CRATE_DOWNLOAD_DIR/334_strings/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/334_strings/source" --strip-components=1

# 335 id=msdos_time name=msdos_time
mkdir -p "$CRATE_DOWNLOAD_DIR/335_msdos_time"
wget -c "https://crates.io/api/v1/crates/msdos_time/0.1.6/download" -O "$CRATE_DOWNLOAD_DIR/335_msdos_time/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/335_msdos_time/source"
tar -xf "$CRATE_DOWNLOAD_DIR/335_msdos_time/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/335_msdos_time/source" --strip-components=1

# 336 id=pest_derive name=pest_derive
mkdir -p "$CRATE_DOWNLOAD_DIR/336_pest_derive"
wget -c "https://crates.io/api/v1/crates/pest_derive/2.0.1/download" -O "$CRATE_DOWNLOAD_DIR/336_pest_derive/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/336_pest_derive/source"
tar -xf "$CRATE_DOWNLOAD_DIR/336_pest_derive/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/336_pest_derive/source" --strip-components=1

# 337 id=osmesa-sys name=osmesa-sys
mkdir -p "$CRATE_DOWNLOAD_DIR/337_osmesa-sys"
wget -c "https://crates.io/api/v1/crates/osmesa-sys/0.1.2/download" -O "$CRATE_DOWNLOAD_DIR/337_osmesa-sys/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/337_osmesa-sys/source"
tar -xf "$CRATE_DOWNLOAD_DIR/337_osmesa-sys/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/337_osmesa-sys/source" --strip-components=1

# 338 id=unix_socket name=unix_socket
mkdir -p "$CRATE_DOWNLOAD_DIR/338_unix_socket"
wget -c "https://crates.io/api/v1/crates/unix_socket/0.5.0/download" -O "$CRATE_DOWNLOAD_DIR/338_unix_socket/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/338_unix_socket/source"
tar -xf "$CRATE_DOWNLOAD_DIR/338_unix_socket/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/338_unix_socket/source" --strip-components=1

# 339 id=openssl-verify name=openssl-verify
mkdir -p "$CRATE_DOWNLOAD_DIR/339_openssl-verify"
wget -c "https://crates.io/api/v1/crates/openssl-verify/0.2.0/download" -O "$CRATE_DOWNLOAD_DIR/339_openssl-verify/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/339_openssl-verify/source"
tar -xf "$CRATE_DOWNLOAD_DIR/339_openssl-verify/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/339_openssl-verify/source" --strip-components=1

# 340 id=hamcrest name=hamcrest
mkdir -p "$CRATE_DOWNLOAD_DIR/340_hamcrest"
wget -c "https://crates.io/api/v1/crates/hamcrest/0.1.5/download" -O "$CRATE_DOWNLOAD_DIR/340_hamcrest/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/340_hamcrest/source"
tar -xf "$CRATE_DOWNLOAD_DIR/340_hamcrest/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/340_hamcrest/source" --strip-components=1

# 341 id=winit name=winit
mkdir -p "$CRATE_DOWNLOAD_DIR/341_winit"
wget -c "https://crates.io/api/v1/crates/winit/0.17.2/download" -O "$CRATE_DOWNLOAD_DIR/341_winit/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/341_winit/source"
tar -xf "$CRATE_DOWNLOAD_DIR/341_winit/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/341_winit/source" --strip-components=1

# 342 id=euclid name=euclid
mkdir -p "$CRATE_DOWNLOAD_DIR/342_euclid"
wget -c "https://crates.io/api/v1/crates/euclid/0.19.2/download" -O "$CRATE_DOWNLOAD_DIR/342_euclid/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/342_euclid/source"
tar -xf "$CRATE_DOWNLOAD_DIR/342_euclid/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/342_euclid/source" --strip-components=1

# 343 id=clippy_lints name=clippy_lints
mkdir -p "$CRATE_DOWNLOAD_DIR/343_clippy_lints"
wget -c "https://crates.io/api/v1/crates/clippy_lints/0.0.212/download" -O "$CRATE_DOWNLOAD_DIR/343_clippy_lints/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/343_clippy_lints/source"
tar -xf "$CRATE_DOWNLOAD_DIR/343_clippy_lints/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/343_clippy_lints/source" --strip-components=1

# 344 id=colored name=colored
mkdir -p "$CRATE_DOWNLOAD_DIR/344_colored"
wget -c "https://crates.io/api/v1/crates/colored/1.6.1/download" -O "$CRATE_DOWNLOAD_DIR/344_colored/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/344_colored/source"
tar -xf "$CRATE_DOWNLOAD_DIR/344_colored/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/344_colored/source" --strip-components=1

# 345 id=block-buffer name=block-buffer
mkdir -p "$CRATE_DOWNLOAD_DIR/345_block-buffer"
wget -c "https://crates.io/api/v1/crates/block-buffer/0.7.0/download" -O "$CRATE_DOWNLOAD_DIR/345_block-buffer/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/345_block-buffer/source"
tar -xf "$CRATE_DOWNLOAD_DIR/345_block-buffer/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/345_block-buffer/source" --strip-components=1

# 346 id=want name=want
mkdir -p "$CRATE_DOWNLOAD_DIR/346_want"
wget -c "https://crates.io/api/v1/crates/want/0.0.6/download" -O "$CRATE_DOWNLOAD_DIR/346_want/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/346_want/source"
tar -xf "$CRATE_DOWNLOAD_DIR/346_want/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/346_want/source" --strip-components=1

# 347 id=try-lock name=try-lock
mkdir -p "$CRATE_DOWNLOAD_DIR/347_try-lock"
wget -c "https://crates.io/api/v1/crates/try-lock/0.2.2/download" -O "$CRATE_DOWNLOAD_DIR/347_try-lock/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/347_try-lock/source"
tar -xf "$CRATE_DOWNLOAD_DIR/347_try-lock/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/347_try-lock/source" --strip-components=1

# 348 id=cgmath name=cgmath
mkdir -p "$CRATE_DOWNLOAD_DIR/348_cgmath"
wget -c "https://crates.io/api/v1/crates/cgmath/0.16.1/download" -O "$CRATE_DOWNLOAD_DIR/348_cgmath/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/348_cgmath/source"
tar -xf "$CRATE_DOWNLOAD_DIR/348_cgmath/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/348_cgmath/source" --strip-components=1

# 349 id=skeptic name=skeptic
mkdir -p "$CRATE_DOWNLOAD_DIR/349_skeptic"
wget -c "https://crates.io/api/v1/crates/skeptic/0.13.3/download" -O "$CRATE_DOWNLOAD_DIR/349_skeptic/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/349_skeptic/source"
tar -xf "$CRATE_DOWNLOAD_DIR/349_skeptic/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/349_skeptic/source" --strip-components=1

# 350 id=serde_cbor name=serde_cbor
mkdir -p "$CRATE_DOWNLOAD_DIR/350_serde_cbor"
wget -c "https://crates.io/api/v1/crates/serde_cbor/0.9.0/download" -O "$CRATE_DOWNLOAD_DIR/350_serde_cbor/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/350_serde_cbor/source"
tar -xf "$CRATE_DOWNLOAD_DIR/350_serde_cbor/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/350_serde_cbor/source" --strip-components=1

# 351 id=lru-cache name=lru-cache
mkdir -p "$CRATE_DOWNLOAD_DIR/351_lru-cache"
wget -c "https://crates.io/api/v1/crates/lru-cache/0.1.1/download" -O "$CRATE_DOWNLOAD_DIR/351_lru-cache/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/351_lru-cache/source"
tar -xf "$CRATE_DOWNLOAD_DIR/351_lru-cache/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/351_lru-cache/source" --strip-components=1

# 352 id=wayland-sys name=wayland-sys
mkdir -p "$CRATE_DOWNLOAD_DIR/352_wayland-sys"
wget -c "https://crates.io/api/v1/crates/wayland-sys/0.21.2/download" -O "$CRATE_DOWNLOAD_DIR/352_wayland-sys/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/352_wayland-sys/source"
tar -xf "$CRATE_DOWNLOAD_DIR/352_wayland-sys/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/352_wayland-sys/source" --strip-components=1

# 353 id=threadpool name=threadpool
mkdir -p "$CRATE_DOWNLOAD_DIR/353_threadpool"
wget -c "https://crates.io/api/v1/crates/threadpool/1.7.1/download" -O "$CRATE_DOWNLOAD_DIR/353_threadpool/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/353_threadpool/source"
tar -xf "$CRATE_DOWNLOAD_DIR/353_threadpool/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/353_threadpool/source" --strip-components=1

# 354 id=dlib name=dlib
mkdir -p "$CRATE_DOWNLOAD_DIR/354_dlib"
wget -c "https://crates.io/api/v1/crates/dlib/0.4.1/download" -O "$CRATE_DOWNLOAD_DIR/354_dlib/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/354_dlib/source"
tar -xf "$CRATE_DOWNLOAD_DIR/354_dlib/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/354_dlib/source" --strip-components=1

# 355 id=wayland-scanner name=wayland-scanner
mkdir -p "$CRATE_DOWNLOAD_DIR/355_wayland-scanner"
wget -c "https://crates.io/api/v1/crates/wayland-scanner/0.21.2/download" -O "$CRATE_DOWNLOAD_DIR/355_wayland-scanner/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/355_wayland-scanner/source"
tar -xf "$CRATE_DOWNLOAD_DIR/355_wayland-scanner/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/355_wayland-scanner/source" --strip-components=1

# 356 id=tokio-uds name=tokio-uds
mkdir -p "$CRATE_DOWNLOAD_DIR/356_tokio-uds"
wget -c "https://crates.io/api/v1/crates/tokio-uds/0.2.2/download" -O "$CRATE_DOWNLOAD_DIR/356_tokio-uds/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/356_tokio-uds/source"
tar -xf "$CRATE_DOWNLOAD_DIR/356_tokio-uds/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/356_tokio-uds/source" --strip-components=1

# 357 id=approx name=approx
mkdir -p "$CRATE_DOWNLOAD_DIR/357_approx"
wget -c "https://crates.io/api/v1/crates/approx/0.3.0/download" -O "$CRATE_DOWNLOAD_DIR/357_approx/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/357_approx/source"
tar -xf "$CRATE_DOWNLOAD_DIR/357_approx/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/357_approx/source" --strip-components=1

# 358 id=router name=router
mkdir -p "$CRATE_DOWNLOAD_DIR/358_router"
wget -c "https://crates.io/api/v1/crates/router/0.6.0/download" -O "$CRATE_DOWNLOAD_DIR/358_router/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/358_router/source"
tar -xf "$CRATE_DOWNLOAD_DIR/358_router/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/358_router/source" --strip-components=1

# 359 id=pretty_assertions name=pretty_assertions
mkdir -p "$CRATE_DOWNLOAD_DIR/359_pretty_assertions"
wget -c "https://crates.io/api/v1/crates/pretty_assertions/0.5.1/download" -O "$CRATE_DOWNLOAD_DIR/359_pretty_assertions/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/359_pretty_assertions/source"
tar -xf "$CRATE_DOWNLOAD_DIR/359_pretty_assertions/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/359_pretty_assertions/source" --strip-components=1

# 360 id=route-recognizer name=route-recognizer
mkdir -p "$CRATE_DOWNLOAD_DIR/360_route-recognizer"
wget -c "https://crates.io/api/v1/crates/route-recognizer/0.1.12/download" -O "$CRATE_DOWNLOAD_DIR/360_route-recognizer/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/360_route-recognizer/source"
tar -xf "$CRATE_DOWNLOAD_DIR/360_route-recognizer/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/360_route-recognizer/source" --strip-components=1

# 361 id=md5 name=md5
mkdir -p "$CRATE_DOWNLOAD_DIR/361_md5"
wget -c "https://crates.io/api/v1/crates/md5/0.5.0/download" -O "$CRATE_DOWNLOAD_DIR/361_md5/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/361_md5/source"
tar -xf "$CRATE_DOWNLOAD_DIR/361_md5/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/361_md5/source" --strip-components=1

# 362 id=ena name=ena
mkdir -p "$CRATE_DOWNLOAD_DIR/362_ena"
wget -c "https://crates.io/api/v1/crates/ena/0.10.1/download" -O "$CRATE_DOWNLOAD_DIR/362_ena/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/362_ena/source"
tar -xf "$CRATE_DOWNLOAD_DIR/362_ena/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/362_ena/source" --strip-components=1

# 363 id=ar name=ar
mkdir -p "$CRATE_DOWNLOAD_DIR/363_ar"
wget -c "https://crates.io/api/v1/crates/ar/0.6.0/download" -O "$CRATE_DOWNLOAD_DIR/363_ar/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/363_ar/source"
tar -xf "$CRATE_DOWNLOAD_DIR/363_ar/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/363_ar/source" --strip-components=1

# 364 id=wayland-kbd name=wayland-kbd
mkdir -p "$CRATE_DOWNLOAD_DIR/364_wayland-kbd"
wget -c "https://crates.io/api/v1/crates/wayland-kbd/0.13.1/download" -O "$CRATE_DOWNLOAD_DIR/364_wayland-kbd/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/364_wayland-kbd/source"
tar -xf "$CRATE_DOWNLOAD_DIR/364_wayland-kbd/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/364_wayland-kbd/source" --strip-components=1

# 365 id=arrayref name=arrayref
mkdir -p "$CRATE_DOWNLOAD_DIR/365_arrayref"
wget -c "https://crates.io/api/v1/crates/arrayref/0.3.5/download" -O "$CRATE_DOWNLOAD_DIR/365_arrayref/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/365_arrayref/source"
tar -xf "$CRATE_DOWNLOAD_DIR/365_arrayref/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/365_arrayref/source" --strip-components=1

# 366 id=log_settings name=log_settings
mkdir -p "$CRATE_DOWNLOAD_DIR/366_log_settings"
wget -c "https://crates.io/api/v1/crates/log_settings/0.1.2/download" -O "$CRATE_DOWNLOAD_DIR/366_log_settings/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/366_log_settings/source"
tar -xf "$CRATE_DOWNLOAD_DIR/366_log_settings/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/366_log_settings/source" --strip-components=1

# 367 id=hyper-native-tls name=hyper-native-tls
mkdir -p "$CRATE_DOWNLOAD_DIR/367_hyper-native-tls"
wget -c "https://crates.io/api/v1/crates/hyper-native-tls/0.3.0/download" -O "$CRATE_DOWNLOAD_DIR/367_hyper-native-tls/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/367_hyper-native-tls/source"
tar -xf "$CRATE_DOWNLOAD_DIR/367_hyper-native-tls/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/367_hyper-native-tls/source" --strip-components=1

# 368 id=core-graphics name=core-graphics
mkdir -p "$CRATE_DOWNLOAD_DIR/368_core-graphics"
wget -c "https://crates.io/api/v1/crates/core-graphics/0.17.2/download" -O "$CRATE_DOWNLOAD_DIR/368_core-graphics/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/368_core-graphics/source"
tar -xf "$CRATE_DOWNLOAD_DIR/368_core-graphics/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/368_core-graphics/source" --strip-components=1

# 369 id=tiny_http name=tiny_http
mkdir -p "$CRATE_DOWNLOAD_DIR/369_tiny_http"
wget -c "https://crates.io/api/v1/crates/tiny_http/0.6.0/download" -O "$CRATE_DOWNLOAD_DIR/369_tiny_http/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/369_tiny_http/source"
tar -xf "$CRATE_DOWNLOAD_DIR/369_tiny_http/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/369_tiny_http/source" --strip-components=1

# 370 id=psapi-sys name=psapi-sys
mkdir -p "$CRATE_DOWNLOAD_DIR/370_psapi-sys"
wget -c "https://crates.io/api/v1/crates/psapi-sys/0.1.1/download" -O "$CRATE_DOWNLOAD_DIR/370_psapi-sys/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/370_psapi-sys/source"
tar -xf "$CRATE_DOWNLOAD_DIR/370_psapi-sys/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/370_psapi-sys/source" --strip-components=1

# 371 id=http name=http
mkdir -p "$CRATE_DOWNLOAD_DIR/371_http"
wget -c "https://crates.io/api/v1/crates/http/0.1.13/download" -O "$CRATE_DOWNLOAD_DIR/371_http/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/371_http/source"
tar -xf "$CRATE_DOWNLOAD_DIR/371_http/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/371_http/source" --strip-components=1

# 372 id=slog name=slog
mkdir -p "$CRATE_DOWNLOAD_DIR/372_slog"
wget -c "https://crates.io/api/v1/crates/slog/2.4.1/download" -O "$CRATE_DOWNLOAD_DIR/372_slog/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/372_slog/source"
tar -xf "$CRATE_DOWNLOAD_DIR/372_slog/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/372_slog/source" --strip-components=1

# 373 id=chunked_transfer name=chunked_transfer
mkdir -p "$CRATE_DOWNLOAD_DIR/373_chunked_transfer"
wget -c "https://crates.io/api/v1/crates/chunked_transfer/0.3.1/download" -O "$CRATE_DOWNLOAD_DIR/373_chunked_transfer/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/373_chunked_transfer/source"
tar -xf "$CRATE_DOWNLOAD_DIR/373_chunked_transfer/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/373_chunked_transfer/source" --strip-components=1

# 374 id=wayland-window name=wayland-window
mkdir -p "$CRATE_DOWNLOAD_DIR/374_wayland-window"
wget -c "https://crates.io/api/v1/crates/wayland-window/0.13.3/download" -O "$CRATE_DOWNLOAD_DIR/374_wayland-window/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/374_wayland-window/source"
tar -xf "$CRATE_DOWNLOAD_DIR/374_wayland-window/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/374_wayland-window/source" --strip-components=1

# 375 id=crossbeam-channel name=crossbeam-channel
mkdir -p "$CRATE_DOWNLOAD_DIR/375_crossbeam-channel"
wget -c "https://crates.io/api/v1/crates/crossbeam-channel/0.2.6/download" -O "$CRATE_DOWNLOAD_DIR/375_crossbeam-channel/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/375_crossbeam-channel/source"
tar -xf "$CRATE_DOWNLOAD_DIR/375_crossbeam-channel/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/375_crossbeam-channel/source" --strip-components=1

# 376 id=notify name=notify
mkdir -p "$CRATE_DOWNLOAD_DIR/376_notify"
wget -c "https://crates.io/api/v1/crates/notify/4.0.6/download" -O "$CRATE_DOWNLOAD_DIR/376_notify/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/376_notify/source"
tar -xf "$CRATE_DOWNLOAD_DIR/376_notify/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/376_notify/source" --strip-components=1

# 377 id=bzip2-sys name=bzip2-sys
mkdir -p "$CRATE_DOWNLOAD_DIR/377_bzip2-sys"
wget -c "https://crates.io/api/v1/crates/bzip2-sys/0.1.6/download" -O "$CRATE_DOWNLOAD_DIR/377_bzip2-sys/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/377_bzip2-sys/source"
tar -xf "$CRATE_DOWNLOAD_DIR/377_bzip2-sys/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/377_bzip2-sys/source" --strip-components=1

# 378 id=toml-query name=toml-query
mkdir -p "$CRATE_DOWNLOAD_DIR/378_toml-query"
wget -c "https://crates.io/api/v1/crates/toml-query/0.7.0/download" -O "$CRATE_DOWNLOAD_DIR/378_toml-query/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/378_toml-query/source"
tar -xf "$CRATE_DOWNLOAD_DIR/378_toml-query/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/378_toml-query/source" --strip-components=1

# 379 id=is-match name=is-match
mkdir -p "$CRATE_DOWNLOAD_DIR/379_is-match"
wget -c "https://crates.io/api/v1/crates/is-match/0.1.0/download" -O "$CRATE_DOWNLOAD_DIR/379_is-match/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/379_is-match/source"
tar -xf "$CRATE_DOWNLOAD_DIR/379_is-match/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/379_is-match/source" --strip-components=1

# 380 id=persistent name=persistent
mkdir -p "$CRATE_DOWNLOAD_DIR/380_persistent"
wget -c "https://crates.io/api/v1/crates/persistent/0.4.0/download" -O "$CRATE_DOWNLOAD_DIR/380_persistent/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/380_persistent/source"
tar -xf "$CRATE_DOWNLOAD_DIR/380_persistent/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/380_persistent/source" --strip-components=1

# 381 id=cssparser name=cssparser
mkdir -p "$CRATE_DOWNLOAD_DIR/381_cssparser"
wget -c "https://crates.io/api/v1/crates/cssparser/0.24.1/download" -O "$CRATE_DOWNLOAD_DIR/381_cssparser/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/381_cssparser/source"
tar -xf "$CRATE_DOWNLOAD_DIR/381_cssparser/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/381_cssparser/source" --strip-components=1

# 382 id=bytecount name=bytecount
mkdir -p "$CRATE_DOWNLOAD_DIR/382_bytecount"
wget -c "https://crates.io/api/v1/crates/bytecount/0.3.2/download" -O "$CRATE_DOWNLOAD_DIR/382_bytecount/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/382_bytecount/source"
tar -xf "$CRATE_DOWNLOAD_DIR/382_bytecount/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/382_bytecount/source" --strip-components=1

# 383 id=bzip2 name=bzip2
mkdir -p "$CRATE_DOWNLOAD_DIR/383_bzip2"
wget -c "https://crates.io/api/v1/crates/bzip2/0.3.3/download" -O "$CRATE_DOWNLOAD_DIR/383_bzip2/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/383_bzip2/source"
tar -xf "$CRATE_DOWNLOAD_DIR/383_bzip2/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/383_bzip2/source" --strip-components=1

# 384 id=crates-io name=crates-io
mkdir -p "$CRATE_DOWNLOAD_DIR/384_crates-io"
wget -c "https://crates.io/api/v1/crates/crates-io/0.18.0/download" -O "$CRATE_DOWNLOAD_DIR/384_crates-io/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/384_crates-io/source"
tar -xf "$CRATE_DOWNLOAD_DIR/384_crates-io/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/384_crates-io/source" --strip-components=1

# 385 id=crypto-mac name=crypto-mac
mkdir -p "$CRATE_DOWNLOAD_DIR/385_crypto-mac"
wget -c "https://crates.io/api/v1/crates/crypto-mac/0.7.0/download" -O "$CRATE_DOWNLOAD_DIR/385_crypto-mac/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/385_crypto-mac/source"
tar -xf "$CRATE_DOWNLOAD_DIR/385_crypto-mac/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/385_crypto-mac/source" --strip-components=1

# 386 id=custom_derive name=custom_derive
mkdir -p "$CRATE_DOWNLOAD_DIR/386_custom_derive"
wget -c "https://crates.io/api/v1/crates/custom_derive/0.1.7/download" -O "$CRATE_DOWNLOAD_DIR/386_custom_derive/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/386_custom_derive/source"
tar -xf "$CRATE_DOWNLOAD_DIR/386_custom_derive/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/386_custom_derive/source" --strip-components=1

# 387 id=rustc-ap-rustc_target name=rustc-ap-rustc_target
mkdir -p "$CRATE_DOWNLOAD_DIR/387_rustc-ap-rustc_target"
wget -c "https://crates.io/api/v1/crates/rustc-ap-rustc_target/274.0.0/download" -O "$CRATE_DOWNLOAD_DIR/387_rustc-ap-rustc_target/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/387_rustc-ap-rustc_target/source"
tar -xf "$CRATE_DOWNLOAD_DIR/387_rustc-ap-rustc_target/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/387_rustc-ap-rustc_target/source" --strip-components=1

# 388 id=quasi_macros name=quasi_macros
mkdir -p "$CRATE_DOWNLOAD_DIR/388_quasi_macros"
wget -c "https://crates.io/api/v1/crates/quasi_macros/0.32.0/download" -O "$CRATE_DOWNLOAD_DIR/388_quasi_macros/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/388_quasi_macros/source"
tar -xf "$CRATE_DOWNLOAD_DIR/388_quasi_macros/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/388_quasi_macros/source" --strip-components=1

# 389 id=xdg name=xdg
mkdir -p "$CRATE_DOWNLOAD_DIR/389_xdg"
wget -c "https://crates.io/api/v1/crates/xdg/2.1.0/download" -O "$CRATE_DOWNLOAD_DIR/389_xdg/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/389_xdg/source"
tar -xf "$CRATE_DOWNLOAD_DIR/389_xdg/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/389_xdg/source" --strip-components=1

# 390 id=cocoa name=cocoa
mkdir -p "$CRATE_DOWNLOAD_DIR/390_cocoa"
wget -c "https://crates.io/api/v1/crates/cocoa/0.18.1/download" -O "$CRATE_DOWNLOAD_DIR/390_cocoa/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/390_cocoa/source"
tar -xf "$CRATE_DOWNLOAD_DIR/390_cocoa/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/390_cocoa/source" --strip-components=1

# 391 id=shell32-sys name=shell32-sys
mkdir -p "$CRATE_DOWNLOAD_DIR/391_shell32-sys"
wget -c "https://crates.io/api/v1/crates/shell32-sys/0.1.2/download" -O "$CRATE_DOWNLOAD_DIR/391_shell32-sys/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/391_shell32-sys/source"
tar -xf "$CRATE_DOWNLOAD_DIR/391_shell32-sys/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/391_shell32-sys/source" --strip-components=1

# 392 id=serde_test name=serde_test
mkdir -p "$CRATE_DOWNLOAD_DIR/392_serde_test"
wget -c "https://crates.io/api/v1/crates/serde_test/1.0.80/download" -O "$CRATE_DOWNLOAD_DIR/392_serde_test/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/392_serde_test/source"
tar -xf "$CRATE_DOWNLOAD_DIR/392_serde_test/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/392_serde_test/source" --strip-components=1

# 393 id=hmac name=hmac
mkdir -p "$CRATE_DOWNLOAD_DIR/393_hmac"
wget -c "https://crates.io/api/v1/crates/hmac/0.7.0/download" -O "$CRATE_DOWNLOAD_DIR/393_hmac/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/393_hmac/source"
tar -xf "$CRATE_DOWNLOAD_DIR/393_hmac/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/393_hmac/source" --strip-components=1

# 394 id=rls-blacklist name=rls-blacklist
mkdir -p "$CRATE_DOWNLOAD_DIR/394_rls-blacklist"
wget -c "https://crates.io/api/v1/crates/rls-blacklist/0.1.2/download" -O "$CRATE_DOWNLOAD_DIR/394_rls-blacklist/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/394_rls-blacklist/source"
tar -xf "$CRATE_DOWNLOAD_DIR/394_rls-blacklist/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/394_rls-blacklist/source" --strip-components=1

# 395 id=indexmap name=indexmap
mkdir -p "$CRATE_DOWNLOAD_DIR/395_indexmap"
wget -c "https://crates.io/api/v1/crates/indexmap/1.0.2/download" -O "$CRATE_DOWNLOAD_DIR/395_indexmap/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/395_indexmap/source"
tar -xf "$CRATE_DOWNLOAD_DIR/395_indexmap/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/395_indexmap/source" --strip-components=1

# 396 id=serde_macros name=serde_macros
mkdir -p "$CRATE_DOWNLOAD_DIR/396_serde_macros"
wget -c "https://crates.io/api/v1/crates/serde_macros/0.8.9/download" -O "$CRATE_DOWNLOAD_DIR/396_serde_macros/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/396_serde_macros/source"
tar -xf "$CRATE_DOWNLOAD_DIR/396_serde_macros/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/396_serde_macros/source" --strip-components=1

# 397 id=syslog name=syslog
mkdir -p "$CRATE_DOWNLOAD_DIR/397_syslog"
wget -c "https://crates.io/api/v1/crates/syslog/4.0.1/download" -O "$CRATE_DOWNLOAD_DIR/397_syslog/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/397_syslog/source"
tar -xf "$CRATE_DOWNLOAD_DIR/397_syslog/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/397_syslog/source" --strip-components=1

# 398 id=metadeps name=metadeps
mkdir -p "$CRATE_DOWNLOAD_DIR/398_metadeps"
wget -c "https://crates.io/api/v1/crates/metadeps/1.1.2/download" -O "$CRATE_DOWNLOAD_DIR/398_metadeps/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/398_metadeps/source"
tar -xf "$CRATE_DOWNLOAD_DIR/398_metadeps/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/398_metadeps/source" --strip-components=1

# 399 id=errno name=errno
mkdir -p "$CRATE_DOWNLOAD_DIR/399_errno"
wget -c "https://crates.io/api/v1/crates/errno/0.2.4/download" -O "$CRATE_DOWNLOAD_DIR/399_errno/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/399_errno/source"
tar -xf "$CRATE_DOWNLOAD_DIR/399_errno/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/399_errno/source" --strip-components=1

# 400 id=clang-sys name=clang-sys
mkdir -p "$CRATE_DOWNLOAD_DIR/400_clang-sys"
wget -c "https://crates.io/api/v1/crates/clang-sys/0.26.1/download" -O "$CRATE_DOWNLOAD_DIR/400_clang-sys/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/400_clang-sys/source"
tar -xf "$CRATE_DOWNLOAD_DIR/400_clang-sys/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/400_clang-sys/source" --strip-components=1

# 401 id=webpki name=webpki
mkdir -p "$CRATE_DOWNLOAD_DIR/401_webpki"
wget -c "https://crates.io/api/v1/crates/webpki/0.18.1/download" -O "$CRATE_DOWNLOAD_DIR/401_webpki/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/401_webpki/source"
tar -xf "$CRATE_DOWNLOAD_DIR/401_webpki/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/401_webpki/source" --strip-components=1

# 402 id=rpassword name=rpassword
mkdir -p "$CRATE_DOWNLOAD_DIR/402_rpassword"
wget -c "https://crates.io/api/v1/crates/rpassword/2.0.0/download" -O "$CRATE_DOWNLOAD_DIR/402_rpassword/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/402_rpassword/source"
tar -xf "$CRATE_DOWNLOAD_DIR/402_rpassword/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/402_rpassword/source" --strip-components=1

# 403 id=strum_macros name=strum_macros
mkdir -p "$CRATE_DOWNLOAD_DIR/403_strum_macros"
wget -c "https://crates.io/api/v1/crates/strum_macros/0.11.0/download" -O "$CRATE_DOWNLOAD_DIR/403_strum_macros/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/403_strum_macros/source"
tar -xf "$CRATE_DOWNLOAD_DIR/403_strum_macros/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/403_strum_macros/source" --strip-components=1

# 404 id=fern name=fern
mkdir -p "$CRATE_DOWNLOAD_DIR/404_fern"
wget -c "https://crates.io/api/v1/crates/fern/0.5.6/download" -O "$CRATE_DOWNLOAD_DIR/404_fern/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/404_fern/source"
tar -xf "$CRATE_DOWNLOAD_DIR/404_fern/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/404_fern/source" --strip-components=1

# 405 id=strum name=strum
mkdir -p "$CRATE_DOWNLOAD_DIR/405_strum"
wget -c "https://crates.io/api/v1/crates/strum/0.11.0/download" -O "$CRATE_DOWNLOAD_DIR/405_strum/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/405_strum/source"
tar -xf "$CRATE_DOWNLOAD_DIR/405_strum/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/405_strum/source" --strip-components=1

# 406 id=ammonia name=ammonia
mkdir -p "$CRATE_DOWNLOAD_DIR/406_ammonia"
wget -c "https://crates.io/api/v1/crates/ammonia/1.2.0/download" -O "$CRATE_DOWNLOAD_DIR/406_ammonia/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/406_ammonia/source"
tar -xf "$CRATE_DOWNLOAD_DIR/406_ammonia/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/406_ammonia/source" --strip-components=1

# 407 id=bodyparser name=bodyparser
mkdir -p "$CRATE_DOWNLOAD_DIR/407_bodyparser"
wget -c "https://crates.io/api/v1/crates/bodyparser/0.8.0/download" -O "$CRATE_DOWNLOAD_DIR/407_bodyparser/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/407_bodyparser/source"
tar -xf "$CRATE_DOWNLOAD_DIR/407_bodyparser/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/407_bodyparser/source" --strip-components=1

# 408 id=objc name=objc
mkdir -p "$CRATE_DOWNLOAD_DIR/408_objc"
wget -c "https://crates.io/api/v1/crates/objc/0.2.5/download" -O "$CRATE_DOWNLOAD_DIR/408_objc/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/408_objc/source"
tar -xf "$CRATE_DOWNLOAD_DIR/408_objc/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/408_objc/source" --strip-components=1

# 409 id=termios name=termios
mkdir -p "$CRATE_DOWNLOAD_DIR/409_termios"
wget -c "https://crates.io/api/v1/crates/termios/0.3.1/download" -O "$CRATE_DOWNLOAD_DIR/409_termios/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/409_termios/source"
tar -xf "$CRATE_DOWNLOAD_DIR/409_termios/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/409_termios/source" --strip-components=1

# 410 id=inotify name=inotify
mkdir -p "$CRATE_DOWNLOAD_DIR/410_inotify"
wget -c "https://crates.io/api/v1/crates/inotify/0.6.1/download" -O "$CRATE_DOWNLOAD_DIR/410_inotify/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/410_inotify/source"
tar -xf "$CRATE_DOWNLOAD_DIR/410_inotify/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/410_inotify/source" --strip-components=1

# 411 id=vergen name=vergen
mkdir -p "$CRATE_DOWNLOAD_DIR/411_vergen"
wget -c "https://crates.io/api/v1/crates/vergen/3.0.4/download" -O "$CRATE_DOWNLOAD_DIR/411_vergen/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/411_vergen/source"
tar -xf "$CRATE_DOWNLOAD_DIR/411_vergen/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/411_vergen/source" --strip-components=1

# 412 id=rustc-ap-arena name=rustc-ap-arena
mkdir -p "$CRATE_DOWNLOAD_DIR/412_rustc-ap-arena"
wget -c "https://crates.io/api/v1/crates/rustc-ap-arena/274.0.0/download" -O "$CRATE_DOWNLOAD_DIR/412_rustc-ap-arena/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/412_rustc-ap-arena/source"
tar -xf "$CRATE_DOWNLOAD_DIR/412_rustc-ap-arena/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/412_rustc-ap-arena/source" --strip-components=1

# 413 id=bindgen name=bindgen
mkdir -p "$CRATE_DOWNLOAD_DIR/413_bindgen"
wget -c "https://crates.io/api/v1/crates/bindgen/0.43.0/download" -O "$CRATE_DOWNLOAD_DIR/413_bindgen/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/413_bindgen/source"
tar -xf "$CRATE_DOWNLOAD_DIR/413_bindgen/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/413_bindgen/source" --strip-components=1

# 414 id=assert_cli name=assert_cli
mkdir -p "$CRATE_DOWNLOAD_DIR/414_assert_cli"
wget -c "https://crates.io/api/v1/crates/assert_cli/0.6.3/download" -O "$CRATE_DOWNLOAD_DIR/414_assert_cli/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/414_assert_cli/source"
tar -xf "$CRATE_DOWNLOAD_DIR/414_assert_cli/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/414_assert_cli/source" --strip-components=1

# 415 id=crc16 name=crc16
mkdir -p "$CRATE_DOWNLOAD_DIR/415_crc16"
wget -c "https://crates.io/api/v1/crates/crc16/0.4.0/download" -O "$CRATE_DOWNLOAD_DIR/415_crc16/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/415_crc16/source"
tar -xf "$CRATE_DOWNLOAD_DIR/415_crc16/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/415_crc16/source" --strip-components=1

# 416 id=selectors name=selectors
mkdir -p "$CRATE_DOWNLOAD_DIR/416_selectors"
wget -c "https://crates.io/api/v1/crates/selectors/0.20.0/download" -O "$CRATE_DOWNLOAD_DIR/416_selectors/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/416_selectors/source"
tar -xf "$CRATE_DOWNLOAD_DIR/416_selectors/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/416_selectors/source" --strip-components=1

# 417 id=nalgebra name=nalgebra
mkdir -p "$CRATE_DOWNLOAD_DIR/417_nalgebra"
wget -c "https://crates.io/api/v1/crates/nalgebra/0.16.5/download" -O "$CRATE_DOWNLOAD_DIR/417_nalgebra/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/417_nalgebra/source"
tar -xf "$CRATE_DOWNLOAD_DIR/417_nalgebra/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/417_nalgebra/source" --strip-components=1

# 418 id=malloc_buf name=malloc_buf
mkdir -p "$CRATE_DOWNLOAD_DIR/418_malloc_buf"
wget -c "https://crates.io/api/v1/crates/malloc_buf/1.0.0/download" -O "$CRATE_DOWNLOAD_DIR/418_malloc_buf/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/418_malloc_buf/source"
tar -xf "$CRATE_DOWNLOAD_DIR/418_malloc_buf/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/418_malloc_buf/source" --strip-components=1

# 419 id=target_build_utils name=target_build_utils
mkdir -p "$CRATE_DOWNLOAD_DIR/419_target_build_utils"
wget -c "https://crates.io/api/v1/crates/target_build_utils/0.3.1/download" -O "$CRATE_DOWNLOAD_DIR/419_target_build_utils/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/419_target_build_utils/source"
tar -xf "$CRATE_DOWNLOAD_DIR/419_target_build_utils/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/419_target_build_utils/source" --strip-components=1

# 420 id=elasticlunr-rs name=elasticlunr-rs
mkdir -p "$CRATE_DOWNLOAD_DIR/420_elasticlunr-rs"
wget -c "https://crates.io/api/v1/crates/elasticlunr-rs/2.3.3/download" -O "$CRATE_DOWNLOAD_DIR/420_elasticlunr-rs/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/420_elasticlunr-rs/source"
tar -xf "$CRATE_DOWNLOAD_DIR/420_elasticlunr-rs/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/420_elasticlunr-rs/source" --strip-components=1

# 421 id=rustfix name=rustfix
mkdir -p "$CRATE_DOWNLOAD_DIR/421_rustfix"
wget -c "https://crates.io/api/v1/crates/rustfix/0.4.2/download" -O "$CRATE_DOWNLOAD_DIR/421_rustfix/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/421_rustfix/source"
tar -xf "$CRATE_DOWNLOAD_DIR/421_rustfix/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/421_rustfix/source" --strip-components=1

# 422 id=num-derive name=num-derive
mkdir -p "$CRATE_DOWNLOAD_DIR/422_num-derive"
wget -c "https://crates.io/api/v1/crates/num-derive/0.2.3/download" -O "$CRATE_DOWNLOAD_DIR/422_num-derive/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/422_num-derive/source"
tar -xf "$CRATE_DOWNLOAD_DIR/422_num-derive/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/422_num-derive/source" --strip-components=1

# 423 id=h2 name=h2
mkdir -p "$CRATE_DOWNLOAD_DIR/423_h2"
wget -c "https://crates.io/api/v1/crates/h2/0.1.13/download" -O "$CRATE_DOWNLOAD_DIR/423_h2/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/423_h2/source"
tar -xf "$CRATE_DOWNLOAD_DIR/423_h2/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/423_h2/source" --strip-components=1

# 424 id=rustls name=rustls
mkdir -p "$CRATE_DOWNLOAD_DIR/424_rustls"
wget -c "https://crates.io/api/v1/crates/rustls/0.14.0/download" -O "$CRATE_DOWNLOAD_DIR/424_rustls/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/424_rustls/source"
tar -xf "$CRATE_DOWNLOAD_DIR/424_rustls/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/424_rustls/source" --strip-components=1

# 425 id=radix_trie name=radix_trie
mkdir -p "$CRATE_DOWNLOAD_DIR/425_radix_trie"
wget -c "https://crates.io/api/v1/crates/radix_trie/0.1.4/download" -O "$CRATE_DOWNLOAD_DIR/425_radix_trie/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/425_radix_trie/source"
tar -xf "$CRATE_DOWNLOAD_DIR/425_radix_trie/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/425_radix_trie/source" --strip-components=1

# 426 id=nibble_vec name=nibble_vec
mkdir -p "$CRATE_DOWNLOAD_DIR/426_nibble_vec"
wget -c "https://crates.io/api/v1/crates/nibble_vec/0.0.4/download" -O "$CRATE_DOWNLOAD_DIR/426_nibble_vec/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/426_nibble_vec/source"
tar -xf "$CRATE_DOWNLOAD_DIR/426_nibble_vec/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/426_nibble_vec/source" --strip-components=1

# 427 id=serde_bytes name=serde_bytes
mkdir -p "$CRATE_DOWNLOAD_DIR/427_serde_bytes"
wget -c "https://crates.io/api/v1/crates/serde_bytes/0.10.4/download" -O "$CRATE_DOWNLOAD_DIR/427_serde_bytes/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/427_serde_bytes/source"
tar -xf "$CRATE_DOWNLOAD_DIR/427_serde_bytes/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/427_serde_bytes/source" --strip-components=1

# 428 id=conv name=conv
mkdir -p "$CRATE_DOWNLOAD_DIR/428_conv"
wget -c "https://crates.io/api/v1/crates/conv/0.3.3/download" -O "$CRATE_DOWNLOAD_DIR/428_conv/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/428_conv/source"
tar -xf "$CRATE_DOWNLOAD_DIR/428_conv/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/428_conv/source" --strip-components=1

# 429 id=cargo name=cargo
mkdir -p "$CRATE_DOWNLOAD_DIR/429_cargo"
wget -c "https://crates.io/api/v1/crates/cargo/0.30.0/download" -O "$CRATE_DOWNLOAD_DIR/429_cargo/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/429_cargo/source"
tar -xf "$CRATE_DOWNLOAD_DIR/429_cargo/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/429_cargo/source" --strip-components=1

# 430 id=draw_state name=draw_state
mkdir -p "$CRATE_DOWNLOAD_DIR/430_draw_state"
wget -c "https://crates.io/api/v1/crates/draw_state/0.8.0/download" -O "$CRATE_DOWNLOAD_DIR/430_draw_state/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/430_draw_state/source"
tar -xf "$CRATE_DOWNLOAD_DIR/430_draw_state/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/430_draw_state/source" --strip-components=1

# 431 id=cgl name=cgl
mkdir -p "$CRATE_DOWNLOAD_DIR/431_cgl"
wget -c "https://crates.io/api/v1/crates/cgl/0.2.3/download" -O "$CRATE_DOWNLOAD_DIR/431_cgl/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/431_cgl/source"
tar -xf "$CRATE_DOWNLOAD_DIR/431_cgl/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/431_cgl/source" --strip-components=1

# 432 id=endian-type name=endian-type
mkdir -p "$CRATE_DOWNLOAD_DIR/432_endian-type"
wget -c "https://crates.io/api/v1/crates/endian-type/0.1.2/download" -O "$CRATE_DOWNLOAD_DIR/432_endian-type/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/432_endian-type/source"
tar -xf "$CRATE_DOWNLOAD_DIR/432_endian-type/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/432_endian-type/source" --strip-components=1

# 433 id=rusttype name=rusttype
mkdir -p "$CRATE_DOWNLOAD_DIR/433_rusttype"
wget -c "https://crates.io/api/v1/crates/rusttype/0.7.2/download" -O "$CRATE_DOWNLOAD_DIR/433_rusttype/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/433_rusttype/source"
tar -xf "$CRATE_DOWNLOAD_DIR/433_rusttype/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/433_rusttype/source" --strip-components=1

# 434 id=environment name=environment
mkdir -p "$CRATE_DOWNLOAD_DIR/434_environment"
wget -c "https://crates.io/api/v1/crates/environment/0.1.1/download" -O "$CRATE_DOWNLOAD_DIR/434_environment/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/434_environment/source"
tar -xf "$CRATE_DOWNLOAD_DIR/434_environment/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/434_environment/source" --strip-components=1

# 435 id=extprim name=extprim
mkdir -p "$CRATE_DOWNLOAD_DIR/435_extprim"
wget -c "https://crates.io/api/v1/crates/extprim/1.6.0/download" -O "$CRATE_DOWNLOAD_DIR/435_extprim/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/435_extprim/source"
tar -xf "$CRATE_DOWNLOAD_DIR/435_extprim/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/435_extprim/source" --strip-components=1

# 436 id=libsqlite3-sys name=libsqlite3-sys
mkdir -p "$CRATE_DOWNLOAD_DIR/436_libsqlite3-sys"
wget -c "https://crates.io/api/v1/crates/libsqlite3-sys/0.10.0/download" -O "$CRATE_DOWNLOAD_DIR/436_libsqlite3-sys/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/436_libsqlite3-sys/source"
tar -xf "$CRATE_DOWNLOAD_DIR/436_libsqlite3-sys/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/436_libsqlite3-sys/source" --strip-components=1

# 437 id=tiny-keccak name=tiny-keccak
mkdir -p "$CRATE_DOWNLOAD_DIR/437_tiny-keccak"
wget -c "https://crates.io/api/v1/crates/tiny-keccak/1.4.2/download" -O "$CRATE_DOWNLOAD_DIR/437_tiny-keccak/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/437_tiny-keccak/source"
tar -xf "$CRATE_DOWNLOAD_DIR/437_tiny-keccak/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/437_tiny-keccak/source" --strip-components=1

# 438 id=cloudabi name=cloudabi
mkdir -p "$CRATE_DOWNLOAD_DIR/438_cloudabi"
wget -c "https://crates.io/api/v1/crates/cloudabi/0.0.3/download" -O "$CRATE_DOWNLOAD_DIR/438_cloudabi/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/438_cloudabi/source"
tar -xf "$CRATE_DOWNLOAD_DIR/438_cloudabi/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/438_cloudabi/source" --strip-components=1

# 439 id=slog-term name=slog-term
mkdir -p "$CRATE_DOWNLOAD_DIR/439_slog-term"
wget -c "https://crates.io/api/v1/crates/slog-term/2.4.0/download" -O "$CRATE_DOWNLOAD_DIR/439_slog-term/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/439_slog-term/source"
tar -xf "$CRATE_DOWNLOAD_DIR/439_slog-term/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/439_slog-term/source" --strip-components=1

# 440 id=dotenv name=dotenv
mkdir -p "$CRATE_DOWNLOAD_DIR/440_dotenv"
wget -c "https://crates.io/api/v1/crates/dotenv/0.13.0/download" -O "$CRATE_DOWNLOAD_DIR/440_dotenv/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/440_dotenv/source"
tar -xf "$CRATE_DOWNLOAD_DIR/440_dotenv/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/440_dotenv/source" --strip-components=1

# 441 id=ws name=ws
mkdir -p "$CRATE_DOWNLOAD_DIR/441_ws"
wget -c "https://crates.io/api/v1/crates/ws/0.7.9/download" -O "$CRATE_DOWNLOAD_DIR/441_ws/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/441_ws/source"
tar -xf "$CRATE_DOWNLOAD_DIR/441_ws/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/441_ws/source" --strip-components=1

# 442 id=rustfmt name=rustfmt
mkdir -p "$CRATE_DOWNLOAD_DIR/442_rustfmt"
wget -c "https://crates.io/api/v1/crates/rustfmt/0.10.0/download" -O "$CRATE_DOWNLOAD_DIR/442_rustfmt/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/442_rustfmt/source"
tar -xf "$CRATE_DOWNLOAD_DIR/442_rustfmt/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/442_rustfmt/source" --strip-components=1

# 443 id=string name=string
mkdir -p "$CRATE_DOWNLOAD_DIR/443_string"
wget -c "https://crates.io/api/v1/crates/string/0.1.1/download" -O "$CRATE_DOWNLOAD_DIR/443_string/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/443_string/source"
tar -xf "$CRATE_DOWNLOAD_DIR/443_string/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/443_string/source" --strip-components=1

# 444 id=tokio-current-thread name=tokio-current-thread
mkdir -p "$CRATE_DOWNLOAD_DIR/444_tokio-current-thread"
wget -c "https://crates.io/api/v1/crates/tokio-current-thread/0.1.3/download" -O "$CRATE_DOWNLOAD_DIR/444_tokio-current-thread/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/444_tokio-current-thread/source"
tar -xf "$CRATE_DOWNLOAD_DIR/444_tokio-current-thread/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/444_tokio-current-thread/source" --strip-components=1

# 445 id=procedural-masquerade name=procedural-masquerade
mkdir -p "$CRATE_DOWNLOAD_DIR/445_procedural-masquerade"
wget -c "https://crates.io/api/v1/crates/procedural-masquerade/0.1.6/download" -O "$CRATE_DOWNLOAD_DIR/445_procedural-masquerade/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/445_procedural-masquerade/source"
tar -xf "$CRATE_DOWNLOAD_DIR/445_procedural-masquerade/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/445_procedural-masquerade/source" --strip-components=1

# 446 id=r2d2 name=r2d2
mkdir -p "$CRATE_DOWNLOAD_DIR/446_r2d2"
wget -c "https://crates.io/api/v1/crates/r2d2/0.8.2/download" -O "$CRATE_DOWNLOAD_DIR/446_r2d2/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/446_r2d2/source"
tar -xf "$CRATE_DOWNLOAD_DIR/446_r2d2/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/446_r2d2/source" --strip-components=1

# 447 id=stb_truetype name=stb_truetype
mkdir -p "$CRATE_DOWNLOAD_DIR/447_stb_truetype"
wget -c "https://crates.io/api/v1/crates/stb_truetype/0.2.4/download" -O "$CRATE_DOWNLOAD_DIR/447_stb_truetype/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/447_stb_truetype/source"
tar -xf "$CRATE_DOWNLOAD_DIR/447_stb_truetype/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/447_stb_truetype/source" --strip-components=1

# 448 id=cexpr name=cexpr
mkdir -p "$CRATE_DOWNLOAD_DIR/448_cexpr"
wget -c "https://crates.io/api/v1/crates/cexpr/0.3.3/download" -O "$CRATE_DOWNLOAD_DIR/448_cexpr/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/448_cexpr/source"
tar -xf "$CRATE_DOWNLOAD_DIR/448_cexpr/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/448_cexpr/source" --strip-components=1

# 449 id=diesel name=diesel
mkdir -p "$CRATE_DOWNLOAD_DIR/449_diesel"
wget -c "https://crates.io/api/v1/crates/diesel/1.3.3/download" -O "$CRATE_DOWNLOAD_DIR/449_diesel/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/449_diesel/source"
tar -xf "$CRATE_DOWNLOAD_DIR/449_diesel/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/449_diesel/source" --strip-components=1

# 450 id=tokio-signal name=tokio-signal
mkdir -p "$CRATE_DOWNLOAD_DIR/450_tokio-signal"
wget -c "https://crates.io/api/v1/crates/tokio-signal/0.2.5/download" -O "$CRATE_DOWNLOAD_DIR/450_tokio-signal/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/450_tokio-signal/source"
tar -xf "$CRATE_DOWNLOAD_DIR/450_tokio-signal/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/450_tokio-signal/source" --strip-components=1

# 451 id=gfx name=gfx
mkdir -p "$CRATE_DOWNLOAD_DIR/451_gfx"
wget -c "https://crates.io/api/v1/crates/gfx/0.17.1/download" -O "$CRATE_DOWNLOAD_DIR/451_gfx/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/451_gfx/source"
tar -xf "$CRATE_DOWNLOAD_DIR/451_gfx/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/451_gfx/source" --strip-components=1

# 452 id=security-framework-sys name=security-framework-sys
mkdir -p "$CRATE_DOWNLOAD_DIR/452_security-framework-sys"
wget -c "https://crates.io/api/v1/crates/security-framework-sys/0.2.1/download" -O "$CRATE_DOWNLOAD_DIR/452_security-framework-sys/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/452_security-framework-sys/source"
tar -xf "$CRATE_DOWNLOAD_DIR/452_security-framework-sys/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/452_security-framework-sys/source" --strip-components=1

# 453 id=security-framework name=security-framework
mkdir -p "$CRATE_DOWNLOAD_DIR/453_security-framework"
wget -c "https://crates.io/api/v1/crates/security-framework/0.2.1/download" -O "$CRATE_DOWNLOAD_DIR/453_security-framework/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/453_security-framework/source"
tar -xf "$CRATE_DOWNLOAD_DIR/453_security-framework/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/453_security-framework/source" --strip-components=1

# 454 id=rustc-hash name=rustc-hash
mkdir -p "$CRATE_DOWNLOAD_DIR/454_rustc-hash"
wget -c "https://crates.io/api/v1/crates/rustc-hash/1.0.1/download" -O "$CRATE_DOWNLOAD_DIR/454_rustc-hash/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/454_rustc-hash/source"
tar -xf "$CRATE_DOWNLOAD_DIR/454_rustc-hash/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/454_rustc-hash/source" --strip-components=1

# 455 id=c_vec name=c_vec
mkdir -p "$CRATE_DOWNLOAD_DIR/455_c_vec"
wget -c "https://crates.io/api/v1/crates/c_vec/1.3.2/download" -O "$CRATE_DOWNLOAD_DIR/455_c_vec/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/455_c_vec/source"
tar -xf "$CRATE_DOWNLOAD_DIR/455_c_vec/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/455_c_vec/source" --strip-components=1

# 456 id=rustc-rayon-core name=rustc-rayon-core
mkdir -p "$CRATE_DOWNLOAD_DIR/456_rustc-rayon-core"
wget -c "https://crates.io/api/v1/crates/rustc-rayon-core/0.1.1/download" -O "$CRATE_DOWNLOAD_DIR/456_rustc-rayon-core/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/456_rustc-rayon-core/source"
tar -xf "$CRATE_DOWNLOAD_DIR/456_rustc-rayon-core/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/456_rustc-rayon-core/source" --strip-components=1

# 457 id=rustc-rayon name=rustc-rayon
mkdir -p "$CRATE_DOWNLOAD_DIR/457_rustc-rayon"
wget -c "https://crates.io/api/v1/crates/rustc-rayon/0.1.1/download" -O "$CRATE_DOWNLOAD_DIR/457_rustc-rayon/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/457_rustc-rayon/source"
tar -xf "$CRATE_DOWNLOAD_DIR/457_rustc-rayon/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/457_rustc-rayon/source" --strip-components=1

# 458 id=gfx_gl name=gfx_gl
mkdir -p "$CRATE_DOWNLOAD_DIR/458_gfx_gl"
wget -c "https://crates.io/api/v1/crates/gfx_gl/0.5.0/download" -O "$CRATE_DOWNLOAD_DIR/458_gfx_gl/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/458_gfx_gl/source"
tar -xf "$CRATE_DOWNLOAD_DIR/458_gfx_gl/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/458_gfx_gl/source" --strip-components=1

# 459 id=rmp name=rmp
mkdir -p "$CRATE_DOWNLOAD_DIR/459_rmp"
wget -c "https://crates.io/api/v1/crates/rmp/0.8.7/download" -O "$CRATE_DOWNLOAD_DIR/459_rmp/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/459_rmp/source"
tar -xf "$CRATE_DOWNLOAD_DIR/459_rmp/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/459_rmp/source" --strip-components=1

# 460 id=cssparser-macros name=cssparser-macros
mkdir -p "$CRATE_DOWNLOAD_DIR/460_cssparser-macros"
wget -c "https://crates.io/api/v1/crates/cssparser-macros/0.3.4/download" -O "$CRATE_DOWNLOAD_DIR/460_cssparser-macros/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/460_cssparser-macros/source"
tar -xf "$CRATE_DOWNLOAD_DIR/460_cssparser-macros/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/460_cssparser-macros/source" --strip-components=1

# 461 id=webpki-roots name=webpki-roots
mkdir -p "$CRATE_DOWNLOAD_DIR/461_webpki-roots"
wget -c "https://crates.io/api/v1/crates/webpki-roots/0.15.0/download" -O "$CRATE_DOWNLOAD_DIR/461_webpki-roots/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/461_webpki-roots/source"
tar -xf "$CRATE_DOWNLOAD_DIR/461_webpki-roots/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/461_webpki-roots/source" --strip-components=1

# 462 id=gl name=gl
mkdir -p "$CRATE_DOWNLOAD_DIR/462_gl"
wget -c "https://crates.io/api/v1/crates/gl/0.10.0/download" -O "$CRATE_DOWNLOAD_DIR/462_gl/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/462_gl/source"
tar -xf "$CRATE_DOWNLOAD_DIR/462_gl/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/462_gl/source" --strip-components=1

# 463 id=gfx_device_gl name=gfx_device_gl
mkdir -p "$CRATE_DOWNLOAD_DIR/463_gfx_device_gl"
wget -c "https://crates.io/api/v1/crates/gfx_device_gl/0.15.3/download" -O "$CRATE_DOWNLOAD_DIR/463_gfx_device_gl/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/463_gfx_device_gl/source"
tar -xf "$CRATE_DOWNLOAD_DIR/463_gfx_device_gl/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/463_gfx_device_gl/source" --strip-components=1

# 464 id=multipart name=multipart
mkdir -p "$CRATE_DOWNLOAD_DIR/464_multipart"
wget -c "https://crates.io/api/v1/crates/multipart/0.15.3/download" -O "$CRATE_DOWNLOAD_DIR/464_multipart/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/464_multipart/source"
tar -xf "$CRATE_DOWNLOAD_DIR/464_multipart/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/464_multipart/source" --strip-components=1

# 465 id=dwmapi-sys name=dwmapi-sys
mkdir -p "$CRATE_DOWNLOAD_DIR/465_dwmapi-sys"
wget -c "https://crates.io/api/v1/crates/dwmapi-sys/0.1.1/download" -O "$CRATE_DOWNLOAD_DIR/465_dwmapi-sys/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/465_dwmapi-sys/source"
tar -xf "$CRATE_DOWNLOAD_DIR/465_dwmapi-sys/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/465_dwmapi-sys/source" --strip-components=1

# 466 id=structopt name=structopt
mkdir -p "$CRATE_DOWNLOAD_DIR/466_structopt"
wget -c "https://crates.io/api/v1/crates/structopt/0.2.12/download" -O "$CRATE_DOWNLOAD_DIR/466_structopt/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/466_structopt/source"
tar -xf "$CRATE_DOWNLOAD_DIR/466_structopt/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/466_structopt/source" --strip-components=1

# 467 id=app_units name=app_units
mkdir -p "$CRATE_DOWNLOAD_DIR/467_app_units"
wget -c "https://crates.io/api/v1/crates/app_units/0.7.1/download" -O "$CRATE_DOWNLOAD_DIR/467_app_units/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/467_app_units/source"
tar -xf "$CRATE_DOWNLOAD_DIR/467_app_units/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/467_app_units/source" --strip-components=1

# 468 id=multimap name=multimap
mkdir -p "$CRATE_DOWNLOAD_DIR/468_multimap"
wget -c "https://crates.io/api/v1/crates/multimap/0.4.0/download" -O "$CRATE_DOWNLOAD_DIR/468_multimap/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/468_multimap/source"
tar -xf "$CRATE_DOWNLOAD_DIR/468_multimap/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/468_multimap/source" --strip-components=1

# 469 id=log4rs name=log4rs
mkdir -p "$CRATE_DOWNLOAD_DIR/469_log4rs"
wget -c "https://crates.io/api/v1/crates/log4rs/0.8.1/download" -O "$CRATE_DOWNLOAD_DIR/469_log4rs/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/469_log4rs/source"
tar -xf "$CRATE_DOWNLOAD_DIR/469_log4rs/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/469_log4rs/source" --strip-components=1

# 470 id=igd name=igd
mkdir -p "$CRATE_DOWNLOAD_DIR/470_igd"
wget -c "https://crates.io/api/v1/crates/igd/0.7.0/download" -O "$CRATE_DOWNLOAD_DIR/470_igd/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/470_igd/source"
tar -xf "$CRATE_DOWNLOAD_DIR/470_igd/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/470_igd/source" --strip-components=1

# 471 id=structopt-derive name=structopt-derive
mkdir -p "$CRATE_DOWNLOAD_DIR/471_structopt-derive"
wget -c "https://crates.io/api/v1/crates/structopt-derive/0.2.12/download" -O "$CRATE_DOWNLOAD_DIR/471_structopt-derive/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/471_structopt-derive/source"
tar -xf "$CRATE_DOWNLOAD_DIR/471_structopt-derive/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/471_structopt-derive/source" --strip-components=1

# 472 id=xmltree name=xmltree
mkdir -p "$CRATE_DOWNLOAD_DIR/472_xmltree"
wget -c "https://crates.io/api/v1/crates/xmltree/0.8.0/download" -O "$CRATE_DOWNLOAD_DIR/472_xmltree/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/472_xmltree/source"
tar -xf "$CRATE_DOWNLOAD_DIR/472_xmltree/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/472_xmltree/source" --strip-components=1

# 473 id=hostname name=hostname
mkdir -p "$CRATE_DOWNLOAD_DIR/473_hostname"
wget -c "https://crates.io/api/v1/crates/hostname/0.1.5/download" -O "$CRATE_DOWNLOAD_DIR/473_hostname/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/473_hostname/source"
tar -xf "$CRATE_DOWNLOAD_DIR/473_hostname/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/473_hostname/source" --strip-components=1

# 474 id=parity-wasm name=parity-wasm
mkdir -p "$CRATE_DOWNLOAD_DIR/474_parity-wasm"
wget -c "https://crates.io/api/v1/crates/parity-wasm/0.35.0/download" -O "$CRATE_DOWNLOAD_DIR/474_parity-wasm/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/474_parity-wasm/source"
tar -xf "$CRATE_DOWNLOAD_DIR/474_parity-wasm/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/474_parity-wasm/source" --strip-components=1

# 475 id=os_pipe name=os_pipe
mkdir -p "$CRATE_DOWNLOAD_DIR/475_os_pipe"
wget -c "https://crates.io/api/v1/crates/os_pipe/0.8.0/download" -O "$CRATE_DOWNLOAD_DIR/475_os_pipe/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/475_os_pipe/source"
tar -xf "$CRATE_DOWNLOAD_DIR/475_os_pipe/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/475_os_pipe/source" --strip-components=1

# 476 id=number_prefix name=number_prefix
mkdir -p "$CRATE_DOWNLOAD_DIR/476_number_prefix"
wget -c "https://crates.io/api/v1/crates/number_prefix/0.2.8/download" -O "$CRATE_DOWNLOAD_DIR/476_number_prefix/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/476_number_prefix/source"
tar -xf "$CRATE_DOWNLOAD_DIR/476_number_prefix/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/476_number_prefix/source" --strip-components=1

# 477 id=minifier name=minifier
mkdir -p "$CRATE_DOWNLOAD_DIR/477_minifier"
wget -c "https://crates.io/api/v1/crates/minifier/0.0.20/download" -O "$CRATE_DOWNLOAD_DIR/477_minifier/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/477_minifier/source"
tar -xf "$CRATE_DOWNLOAD_DIR/477_minifier/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/477_minifier/source" --strip-components=1

# 478 id=sequence_trie name=sequence_trie
mkdir -p "$CRATE_DOWNLOAD_DIR/478_sequence_trie"
wget -c "https://crates.io/api/v1/crates/sequence_trie/0.3.5/download" -O "$CRATE_DOWNLOAD_DIR/478_sequence_trie/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/478_sequence_trie/source"
tar -xf "$CRATE_DOWNLOAD_DIR/478_sequence_trie/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/478_sequence_trie/source" --strip-components=1

# 479 id=postgres name=postgres
mkdir -p "$CRATE_DOWNLOAD_DIR/479_postgres"
wget -c "https://crates.io/api/v1/crates/postgres/0.15.2/download" -O "$CRATE_DOWNLOAD_DIR/479_postgres/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/479_postgres/source"
tar -xf "$CRATE_DOWNLOAD_DIR/479_postgres/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/479_postgres/source" --strip-components=1

# 480 id=which name=which
mkdir -p "$CRATE_DOWNLOAD_DIR/480_which"
wget -c "https://crates.io/api/v1/crates/which/2.0.0/download" -O "$CRATE_DOWNLOAD_DIR/480_which/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/480_which/source"
tar -xf "$CRATE_DOWNLOAD_DIR/480_which/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/480_which/source" --strip-components=1

# 481 id=yup-oauth2 name=yup-oauth2
mkdir -p "$CRATE_DOWNLOAD_DIR/481_yup-oauth2"
wget -c "https://crates.io/api/v1/crates/yup-oauth2/1.0.9/download" -O "$CRATE_DOWNLOAD_DIR/481_yup-oauth2/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/481_yup-oauth2/source"
tar -xf "$CRATE_DOWNLOAD_DIR/481_yup-oauth2/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/481_yup-oauth2/source" --strip-components=1

# 482 id=kuchiki name=kuchiki
mkdir -p "$CRATE_DOWNLOAD_DIR/482_kuchiki"
wget -c "https://crates.io/api/v1/crates/kuchiki/0.7.2/download" -O "$CRATE_DOWNLOAD_DIR/482_kuchiki/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/482_kuchiki/source"
tar -xf "$CRATE_DOWNLOAD_DIR/482_kuchiki/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/482_kuchiki/source" --strip-components=1

# 483 id=duct name=duct
mkdir -p "$CRATE_DOWNLOAD_DIR/483_duct"
wget -c "https://crates.io/api/v1/crates/duct/0.11.1/download" -O "$CRATE_DOWNLOAD_DIR/483_duct/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/483_duct/source"
tar -xf "$CRATE_DOWNLOAD_DIR/483_duct/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/483_duct/source" --strip-components=1

# 484 id=mount name=mount
mkdir -p "$CRATE_DOWNLOAD_DIR/484_mount"
wget -c "https://crates.io/api/v1/crates/mount/0.4.0/download" -O "$CRATE_DOWNLOAD_DIR/484_mount/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/484_mount/source"
tar -xf "$CRATE_DOWNLOAD_DIR/484_mount/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/484_mount/source" --strip-components=1

# 485 id=gfx_core name=gfx_core
mkdir -p "$CRATE_DOWNLOAD_DIR/485_gfx_core"
wget -c "https://crates.io/api/v1/crates/gfx_core/0.8.3/download" -O "$CRATE_DOWNLOAD_DIR/485_gfx_core/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/485_gfx_core/source"
tar -xf "$CRATE_DOWNLOAD_DIR/485_gfx_core/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/485_gfx_core/source" --strip-components=1

# 486 id=wayland-protocols name=wayland-protocols
mkdir -p "$CRATE_DOWNLOAD_DIR/486_wayland-protocols"
wget -c "https://crates.io/api/v1/crates/wayland-protocols/0.21.2/download" -O "$CRATE_DOWNLOAD_DIR/486_wayland-protocols/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/486_wayland-protocols/source"
tar -xf "$CRATE_DOWNLOAD_DIR/486_wayland-protocols/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/486_wayland-protocols/source" --strip-components=1

# 487 id=ctrlc name=ctrlc
mkdir -p "$CRATE_DOWNLOAD_DIR/487_ctrlc"
wget -c "https://crates.io/api/v1/crates/ctrlc/3.1.1/download" -O "$CRATE_DOWNLOAD_DIR/487_ctrlc/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/487_ctrlc/source"
tar -xf "$CRATE_DOWNLOAD_DIR/487_ctrlc/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/487_ctrlc/source" --strip-components=1

# 488 id=pistoncore-input name=pistoncore-input
mkdir -p "$CRATE_DOWNLOAD_DIR/488_pistoncore-input"
wget -c "https://crates.io/api/v1/crates/pistoncore-input/0.22.0/download" -O "$CRATE_DOWNLOAD_DIR/488_pistoncore-input/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/488_pistoncore-input/source"
tar -xf "$CRATE_DOWNLOAD_DIR/488_pistoncore-input/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/488_pistoncore-input/source" --strip-components=1

# 489 id=shared_child name=shared_child
mkdir -p "$CRATE_DOWNLOAD_DIR/489_shared_child"
wget -c "https://crates.io/api/v1/crates/shared_child/0.3.3/download" -O "$CRATE_DOWNLOAD_DIR/489_shared_child/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/489_shared_child/source"
tar -xf "$CRATE_DOWNLOAD_DIR/489_shared_child/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/489_shared_child/source" --strip-components=1

# 490 id=csv-core name=csv-core
mkdir -p "$CRATE_DOWNLOAD_DIR/490_csv-core"
wget -c "https://crates.io/api/v1/crates/csv-core/0.1.4/download" -O "$CRATE_DOWNLOAD_DIR/490_csv-core/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/490_csv-core/source"
tar -xf "$CRATE_DOWNLOAD_DIR/490_csv-core/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/490_csv-core/source" --strip-components=1

# 491 id=sdl2-sys name=sdl2-sys
mkdir -p "$CRATE_DOWNLOAD_DIR/491_sdl2-sys"
wget -c "https://crates.io/api/v1/crates/sdl2-sys/0.32.1/download" -O "$CRATE_DOWNLOAD_DIR/491_sdl2-sys/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/491_sdl2-sys/source"
tar -xf "$CRATE_DOWNLOAD_DIR/491_sdl2-sys/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/491_sdl2-sys/source" --strip-components=1

# 492 id=matrixmultiply name=matrixmultiply
mkdir -p "$CRATE_DOWNLOAD_DIR/492_matrixmultiply"
wget -c "https://crates.io/api/v1/crates/matrixmultiply/0.1.14/download" -O "$CRATE_DOWNLOAD_DIR/492_matrixmultiply/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/492_matrixmultiply/source"
tar -xf "$CRATE_DOWNLOAD_DIR/492_matrixmultiply/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/492_matrixmultiply/source" --strip-components=1

# 493 id=serde-value name=serde-value
mkdir -p "$CRATE_DOWNLOAD_DIR/493_serde-value"
wget -c "https://crates.io/api/v1/crates/serde-value/0.5.2/download" -O "$CRATE_DOWNLOAD_DIR/493_serde-value/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/493_serde-value/source"
tar -xf "$CRATE_DOWNLOAD_DIR/493_serde-value/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/493_serde-value/source" --strip-components=1

# 494 id=peeking_take_while name=peeking_take_while
mkdir -p "$CRATE_DOWNLOAD_DIR/494_peeking_take_while"
wget -c "https://crates.io/api/v1/crates/peeking_take_while/0.1.2/download" -O "$CRATE_DOWNLOAD_DIR/494_peeking_take_while/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/494_peeking_take_while/source"
tar -xf "$CRATE_DOWNLOAD_DIR/494_peeking_take_while/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/494_peeking_take_while/source" --strip-components=1

# 495 id=new_debug_unreachable name=new_debug_unreachable
mkdir -p "$CRATE_DOWNLOAD_DIR/495_new_debug_unreachable"
wget -c "https://crates.io/api/v1/crates/new_debug_unreachable/1.0.1/download" -O "$CRATE_DOWNLOAD_DIR/495_new_debug_unreachable/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/495_new_debug_unreachable/source"
tar -xf "$CRATE_DOWNLOAD_DIR/495_new_debug_unreachable/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/495_new_debug_unreachable/source" --strip-components=1

# 496 id=piston-float name=piston-float
mkdir -p "$CRATE_DOWNLOAD_DIR/496_piston-float"
wget -c "https://crates.io/api/v1/crates/piston-float/0.3.0/download" -O "$CRATE_DOWNLOAD_DIR/496_piston-float/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/496_piston-float/source"
tar -xf "$CRATE_DOWNLOAD_DIR/496_piston-float/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/496_piston-float/source" --strip-components=1

# 497 id=chalk-engine name=chalk-engine
mkdir -p "$CRATE_DOWNLOAD_DIR/497_chalk-engine"
wget -c "https://crates.io/api/v1/crates/chalk-engine/0.8.0/download" -O "$CRATE_DOWNLOAD_DIR/497_chalk-engine/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/497_chalk-engine/source"
tar -xf "$CRATE_DOWNLOAD_DIR/497_chalk-engine/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/497_chalk-engine/source" --strip-components=1

# 498 id=expat-sys name=expat-sys
mkdir -p "$CRATE_DOWNLOAD_DIR/498_expat-sys"
wget -c "https://crates.io/api/v1/crates/expat-sys/2.1.6/download" -O "$CRATE_DOWNLOAD_DIR/498_expat-sys/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/498_expat-sys/source"
tar -xf "$CRATE_DOWNLOAD_DIR/498_expat-sys/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/498_expat-sys/source" --strip-components=1

# 499 id=chalk-macros name=chalk-macros
mkdir -p "$CRATE_DOWNLOAD_DIR/499_chalk-macros"
wget -c "https://crates.io/api/v1/crates/chalk-macros/0.1.0/download" -O "$CRATE_DOWNLOAD_DIR/499_chalk-macros/crate.tar.gz"
mkdir -p "$CRATE_DOWNLOAD_DIR/499_chalk-macros/source"
tar -xf "$CRATE_DOWNLOAD_DIR/499_chalk-macros/crate.tar.gz" --directory="$CRATE_DOWNLOAD_DIR/499_chalk-macros/source" --strip-components=1
