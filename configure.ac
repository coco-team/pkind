#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

AC_INIT([KIND], [1], [temesghen-kahsaiazene@uiowa.edu])
AC_CONFIG_SRCDIR([src/pkind.ml])

# default prefix is /usr/local
AC_PREFIX_DEFAULT(/usr/local)

# Checking Ocaml 
AC_PROG_OCAML
if test "x$OCAMLC" = "xno"; then
  AC_MSG_ERROR([You must install the OCaml compiler])
fi

# Checking findlib
AC_PROG_FINDLIB
if test "x$OCAMLFIND" = "xno"; then
   AC_MSG_WARN([You must install OCaml findlib (the ocamlfind command)])
fi

# Checking Yices
AC_CHECK_PROG(yices_enabled,yices,yes)
if test "x$yices_enabled" = "xno"; then
   AC_MSG_ERROR([Yices is not in your path])
fi

# Checking librairies

error_mode=0

AC_CHECK_OCAML_PKG([mpi])
AC_CHECK_OCAML_PKG([extlib])

if test "$OCAML_PKG_mpi" = "no"; then
  AC_MSG_WARN([Unable to find OCaml findlib module 'mpi'. Will be added to the compilation target])
  MPI_LIB=ocamlmpi
  MPI_INC="\"`pwd`/lib\""
else
  MPI_INC="ocamlfind_query \"mpi\""
fi
AC_SUBST(MPI_INC)
AC_SUBST(MPI_LIB)

if test "$OCAML_PKG_extlib" = "no"; then
  AC_MSG_WARN([Unable to find OCaml findlib module 'extlib'. Will be added to the compilation target])
  EXT_LIB=extlib
  EXTLIB_INC="\"`pwd`/lib\""
else
  EXTLIB_INC="ocamlfind_query \"extlib\""
fi
AC_SUBST(EXTLIB_INC)
AC_SUBST(EXT_LIB)


# Checking solvers path
AC_PATH_PROG([Z3_PATH],[z3],[undefined])
AC_SUBST(Z3_PATH)
AC_PATH_PROG([CVC3_PATH],[cvc3],[undefined])
AC_SUBST(CVC3_PATH)
AC_PATH_PROG([CVC4_PATH],[cvc4],[undefined])
AC_SUBST(CVC4_PATH)
AC_PATH_PROG([YICES_PATH],[yices],[undefined])
AC_SUBST(YICES_PATH)
AC_PATH_PROG([KIND_AI_PATH],[kind-ai],[undefined])
AC_SUBST(KIND_AI_PATH)


AC_ARG_WITH([yices_dir],
        [AS_HELP_STRING([--with-yices-dir],
              [specify the path of the yices root directory. It should contain bin/yices])],
        [AS_IF([test "x$with_yices_dir" = xno],
                [AC_MSG_ERROR([Yices path is required])],
                [test "x$with_yices_dir" = xyes],
                [AC_MSG_ERROR([--with-yices-dir=path_to_yices is required])],
                [YICESDIR_PATH=`cd $with_yices_dir; pwd`]
        )],
        [YICESDIR_PATH='error']
)
yicesw_enabled=no
AC_ARG_WITH([yicesw],
        [AS_HELP_STRING([--with-yicesw],
              [requires to compile a wrapper for yices. Need to use --with-yices-dir option])],
        [AS_IF([test "x$YICESDIR_PATH" = xerror],
                [AC_MSG_ERROR([Yices path is required])],
                [yicesw_enabled=yes])],
        [yicesw_enabled=no]
)
AC_SUBST(YICESDIR_PATH)

AC_PATH_PROG([YICESW_PATH],[yicesw],[no])
if test "x$YICESW_PATH x$yicesw_enabled" = "xno xyes"; then
   YICESW_PATH=yicesw
   YICESW_DEP=yicesw
else
   YICESW_DEP=""
fi
AC_SUBST(YICESW_DEP)
AC_SUBST(YICESW_PATH)


AC_ARG_WITH([yicesw_macosx],
    AS_HELP_STRING([--with-yicesw-macosx], 
                   [link yicesw dynamically and with -no_pie (required for Mac OS X)]))


AS_IF([test "x$with_yicesw_macosx" = "xno"], 
      [YICESW_CFLAGS=-static],
      [YICESW_CFLAGS=-Wl,-no_pie])

AC_SUBST(YICESW_CFLAGS)

#check for gmp
AC_ARG_WITH([gmp_path],
       [AS_HELP_STRING([--with-gmp-path],
             [specify the path to the GMP library @<:@default=/usr/lib@:>@])],
       [AS_IF([test "x$with_gmp_path" = xno],
               [AC_MSG_ERROR([GMP library is needed])],
               [test "x$with_gmp_path" = xyes],
               [GMPLIB_PATH=/usr/lib],
               [GMPLIB_PATH=$with_gmp_path]
       )],
       [GMPLIB_PATH=/usr/lib]
)
AC_SUBST(GMPLIB_PATH)

#check for openmpi
AC_ARG_WITH([mpi_path],
       [AS_HELP_STRING([--with-mpi-path],
             [specify the path to the MPI library. libmpi.so should be in mpi-path/lib and mpi.h in mpi-path/include/opennpi @<:@default=/usr@:>@])],
       [AS_IF([test "x$with_mpi_path" = xno],
               [AC_MSG_ERROR([MPI library is needed])],
               [test "x$with_mpi_path" = xyes],
               [MPI_PATH=/usr],
               [MPI_PATH=$with_mpi_path]
       )],
       [MPI_PATH=/usr]
)

AC_ARG_WITH([mpi_include],
       [AS_HELP_STRING([--with-mpi-include],
             [specify the path to the MPI include files @<:@default=/usr/include/openmpi@:>@])],
       [AS_IF([test "x$with_mpi_include" = xno],
               [AC_MSG_ERROR([MPI include files are needed])],
               [test "x$with_mpi_include" = xyes],
               [MPIINCDIR=$MPI_PATH/include/openmpi],
               [MPIINCDIR=$with_mpi_include]
       )],
       [MPIINCDIR=$MPI_PATH/include/openmpi]
)

AC_ARG_WITH([mpi_lib],
       [AS_HELP_STRING([--with-mpi-lib],
             [specify the path to the MPI library files @<:@default=/usr/lib@:>@])],
       [AS_IF([test "x$with_mpi_lib" = xno],
               [AC_MSG_ERROR([MPI library files are needed])],
               [test "x$with_mpi_lib" = xyes],
               [MPILIBDIR=$MPI_PATH/lib],
               [MPILIBDIR=$with_mpi_lib]
       )],
       [MPILIBDIR=$MPI_PATH/lib]
)

AC_SUBST(MPIINCDIR)
AC_SUBST(MPILIBDIR)

AC_SUBST(DEPENDENCIES)



# Instanciation
AC_CONFIG_FILES([Makefile dependencies/Makefile dependencies/ocamlmpi-PKind/Makefile src/myocamlbuild.ml src/solvers_path.ml dependencies/build_yicesw.sh src/Makefile])

AC_OUTPUT
echo "Configure succeed. Run now make and make install."
