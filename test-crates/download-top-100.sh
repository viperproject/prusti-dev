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
