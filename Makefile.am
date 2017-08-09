## Process this file with automake to produce Makefile.in

ACLOCAL_AMFLAGS		= -I meta/autotools
AUTOMAKE_OPTIONS	= foreign
EXTRA_DIST		= README COPYING INSTALL
CLEANFILES		=

## --------------------------------------------------------------------

AM_MAKEINFOFLAGS	= --no-split

info_TEXINFOS		= doc/chez-infix.texi
doc_chez_infix_TEXINFOS	= \
	doc/macros.texi		\
	doc/fdl-1.3.texi	\
	doc/gpl-3.0.texi

#page
#### libraries

lib_infix_pratt_sodir		= $(libdir)/ChezScheme/infix
dist_lib_infix_pratt_so_DATA	= lib/infix/pratt.so
EXTRA_DIST			+= lib/infix/pratt.sls
CLEANFILES			+= lib/infix/pratt.so lib/infix/$(am__dirstamp)

# These compose  the libraries search  path to compile  the libraries.
# The build directories  must come first; the  source directories must
# come last.
#
INFIX_COMPILE_LIBPATH	= $(builddir)/lib:$(srcdir)/lib

CHEZ_COMPILE_ENV	= export CHEZSCHEMELIBDIRS=$(INFIX_COMPILE_LIBPATH); export CHEZSCHEMELIBEXTS=.sls;
CHEZ_COMPILE_FLAGS	= --quiet
CHEZ_COMPILE		= $(CHEZ_PROGRAM) $(CHEZ_COMPILE_FLAGS)

lib/infix/$(am__dirstamp):
	@$(MKDIR_P) lib/infix
	@: > lib/infix/$(am__dirstamp)

lib/infix/pratt.so: lib/infix/pratt.sls lib/infix/$(am__dirstamp)
	$(CHEZ_COMPILE_ENV) \
	echo '(parameterize ((optimize-level 3)) (compile-library "$<" "$@"))' | $(CHEZ_COMPILE)

#page
#### interface to "make check"

# Read "Parallel Test Harness" in the documentation of GNU Automake to
# understand how to use this interface for "make check".

EXTRA_DIST		+= \
	tests/checks.sls	\
	tests/infix-pratt.sps

INFIX_TEST_LIBS		= tests/checks.so
INFIX_TEST_PROGS	= tests/infix-pratt.so

CLEANFILES		+= $(INFIX_TEST_PROGS) $(INFIX_TEST_LIBS) tests/$(am__dirstamp)

# These compose the libraries search path  to compile and run the test
# programs.   The  build  directories  must  come  first;  the  source
# directories must come last.
#
INFIX_CHECK_LIBPATH	= $(builddir)/tests:$(srcdir)/tests:$(builddir)/lib

TESTS			= $(INFIX_TEST_PROGS)
#XFAIL_TESTS		=
TEST_EXTENSIONS		= .so

CHEZ_CHECK_ENV		= export CHEZSCHEMELIBDIRS=$(INFIX_CHECK_LIBPATH); export CHEZSCHEMELIBEXTS=.sls;

# We must make sure that this environment ends with a semicolon!!!
#
AM_TESTS_ENVIRONMENT	= $(CHEZ_CHECK_ENV)
SO_LOG_COMPILER		= $(CHEZ_PROGRAM)
AM_SO_LOG_FLAGS		= --program

## --------------------------------------------------------------------

tests/$(am__dirstamp):
	@$(MKDIR_P) tests
	@: > tests/$(am__dirstamp)

tests/checks.so: tests/checks.sls tests/$(am__dirstamp)
	$(CHEZ_CHECK_ENV) \
	echo '(parameterize ((optimize-level 3)) (compile-library "$<" "$@"))' | $(CHEZ_PROGRAM) -q

tests/infix-pratt.so: tests/infix-pratt.sps tests/checks.so tests/$(am__dirstamp)
	$(CHEZ_CHECK_ENV) \
	echo '(parameterize ((optimize-level 3)) (compile-program "$<" "$@"))' | $(CHEZ_PROGRAM) -q

## --------------------------------------------------------------------
## tests for installed libraries

CHEZ_INSTCHECK_ENV	= export CHEZSCHEMELIBDIRS=$(INFIX_TESTDIR):$(CHEZSCHEMELIBDIRS); export CHEZSCHEMELIBEXTS=.sls;
CHEZ_INSTCHECK_FLAGS	= --program
CHEZ_INSTCHECK_RUN	= $(CHEZ_INSTCHECK_ENV) $(CHEZ_PROGRAM) $(CHEZ_INSTCHECK_FLAGS)

installcheck-local:
	-@for f in $(INFIX_TESTDIR)/*.sps; do $(CHEZ_INSTCHECK_RUN) $$f; done

### end of file
