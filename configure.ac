dnl @configure_input@
dnl

AC_PREREQ([2.69])
AC_INIT([Chez/Infix],[1.0.0],[marco.maggi-ipsu@poste.it],
  [chez-infix],[https://github.com/marcomaggi/chez-infix])
AC_CONFIG_SRCDIR([lib])
AC_CONFIG_MACRO_DIR([meta/autotools])
AC_CONFIG_AUX_DIR([meta/autotools])
AC_CANONICAL_BUILD
AC_CANONICAL_HOST
AC_CANONICAL_TARGET
AM_INIT_AUTOMAKE([foreign dist-xz no-dist-gzip])
AM_MAINTAINER_MODE

AC_PROG_INSTALL
AC_PROG_LN_S
AC_PROG_MAKE_SET
AC_PROG_MKDIR_P

AX_CHEZ_SCHEME

dnl page
dnl Optional features

AS_VAR_SET([INFIX_OPTION_DEBUG],[no])
AC_MSG_CHECKING([whether debugging features are included in compiled Scheme libraries])
AC_ARG_ENABLE([debug],
   [AS_HELP_STRING([--enable-debug],
      [enable compilation of Scheme libraries with debugging features (default is disable)])],
   [AC_MSG_RESULT([$enableval])
    AS_IF([test "z$enableval" = zno],[AS_VAR_SET([INFIX_OPTION_DEBUG],[no])],
          [AS_VAR_SET([INFIX_OPTION_DEBUG],[yes])])],
   [AS_VAR_SET([INFIX_OPTION_DEBUG],[no])
    AC_MSG_RESULT([no])])
AM_CONDITIONAL([WANT_INFIX_OPTION_DEBUG],[test x$INFIX_OPTION_DEBUG = xyes])
AM_COND_IF([WANT_INFIX_OPTION_DEBUG],[AS_VAR_SET(AM_VFLAGS,"$AM_VFLAGS -g")])

dnl page
dnl done

AC_CONFIG_FILES([Makefile])
AC_OUTPUT

dnl end of file
