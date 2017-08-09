# configure.sh --
#

set -xe

prefix=/usr/local
if test -d /lib64
then libdir=${prefix}/lib64
else libdir=${prefix}/lib
fi

../configure \
    --enable-maintainer-mode				\
    --config-cache					\
    --cache-file=../config.cache			\
    --prefix="${prefix}"				\
    --libdir="${libdir}"				\
    "$@"

### end of file
