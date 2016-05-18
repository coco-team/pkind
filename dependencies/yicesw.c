/*
This file is part of the Kind verifier

* Copyright (c) 2007-2009 by the Board of Trustees of the University of Iowa, 
* here after designated as the Copyright Holder.
* All rights reserved.
*
* Redistribution and use in source and binary forms, with or without
* modification, are permitted provided that the following conditions are met:
*     * Redistributions of source code must retain the above copyright
*       notice, this list of conditions and the following disclaimer.
*     * Redistributions in binary form must reproduce the above copyright
*       notice, this list of conditions and the following disclaimer in the
*       documentation and/or other materials provided with the distribution.
*     * Neither the name of the University of Iowa, nor the
*       names of its contributors may be used to endorse or promote products
*       derived from this software without specific prior written permission.
*
* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER ''AS IS'' AND ANY
* EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
* WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
* DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER BE LIABLE FOR ANY
* DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
* (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
* LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
* ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
* (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*/

/* a simple YICES wrapper */
/* input is taken from stdin */

#include <stdio.h>
#include <stdlib.h>
#include "yicesl_c.h"

int main(int argc, char **argv)
{
  int i, numpars, incomment, incmd, ok;
  unsigned long int strpos;
  char* buff;
  yicesl_context ctx = yicesl_mk_context();
  numpars = incomment = incmd = strpos = 0;
  int debug = 0;

  if (argc == 2 && !strcmp(argv[1],"-debug")) {
    debug=1;
  }


  buff = (char*) malloc(100000000*sizeof(char));
  i = getchar();
  while (i != EOF) {

/*
    if (debug) {
      printf("%c",i);
    }
*/

    /* skip all comments */
    if (i == ';') {
      incomment = 1;
    }
    if (incomment) {
      if (i == '\n') {
        incomment = 0;
      }
    } else {
      /* set incmd = 1 if we start in a command */
      if (numpars > 0) {
        incmd = 1;
      } else {
        incmd = 0;
      }
      if (strpos > 99999999) {
        printf("ERROR: input too long (%lu)\n",strpos);
        exit(1);  /* error */
      }

      buff[strpos++] = i;

      if (i == '(') {
        numpars++;
      }
      if (i == ')') {
        numpars--;
      }

      if (numpars == 0 && incmd) {
        buff[strpos++]=0;
        ok = yicesl_read(ctx,buff);
        if (!ok) {
          printf("ERROR: %s\n",yicesl_get_last_error_message());
          exit(1);
        }
        printf("\n\n");
        fflush(stdout);
        strpos = 0;
      }
    }
    i = getchar();
  }

  free(buff);
  return 0;
}
