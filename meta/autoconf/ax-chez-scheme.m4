dnl ax-chez-scheme.m4 --
dnl
dnl Finds Chez Scheme with executable installed as "chez".

AC_DEFUN([AX_CHEZ_SCHEME],
  [AC_CHECK_PROG([CHEZ_PROGRAM],[chez],[chez],[:])])

dnl end of file
dnl Local Variables:
dnl mode: autoconf
dnl End:
