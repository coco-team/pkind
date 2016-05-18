![Screen Shot 2014-06-13 at 12.57.17 PM.png](https://bitbucket.org/repo/pR8ad7/images/1503838948-Screen%20Shot%202014-06-13%20at%2012.57.17%20PM.png)

PKIND is an SMT-based model checker for programs written in the synchronous dataflow programming language Lustre.


## Contents  ##

 * ./bin      -- Contains the executables (pkind, kind-inv, lsimplify)
 * ./src      -- All PKIND source files.
 * ./tests    -- A few example of Lustre programs
 * ./scripts  -- Python scripts to run different tasks using PKIND


## Quick install ##

See the INSTALL file for a full description of the compilation process of PKIND.
For a quick install, issue the following commands:

* `./configure`
* `make`
* `make install`

We recommended to use the Yices wrapper (See the INSTALL file).


## USAGE ##

1. PKIND (model checker) `pkind [OPTIONS] LUSTRE_FILE`


2. LSIMPLIFY (Lustre simplifier) `lsimplify [OPTIONS] LUSTRE_FILE`


3. KIND-INV (Invariant generation)  `kind_inv [-inv_int and/or inv_bool] [OPTIONS] LUSTRE_FILE`


4. Script to run different tasks using PKIND `python scripts/pkind.py [OPTIONS] -f LUSTRE_FILE`


## Lustre files supported by PKIND ##

PKIND currently does not support forward references of nodes.  There is only very limited support for non-linear arithmetic, records, and the "when" operation.

For integer constants, only those with up to nine digits are supported.
For floating-points numbers, only up to nine digits can appear right or
left of the decimal point.  Floating-points number of the form 0.000000E+00
are supported.

Properties to be checked should appear in special comment lines in the body
of the topmost node:

  --!PROPERTY : <lustre property>;

where <lustre property> is a Lustre Boolean expression, ending with a
semicolon.  Multiple property lines are conjoined.


## Contact ##

For more information please contact:

   > Temesghen Kahsai (tkahsai AT sv.cmu.edu or lememta AT gmail.com)