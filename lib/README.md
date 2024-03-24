This folder contains dependencies for Theta.
See [Build.md](../doc/Build.md#dependencies) for more information.

Z3 is licensed under the following license:
```
Z3
Copyright (c) Microsoft Corporation
All rights reserved. 
MIT License

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED *AS IS*, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
```

GNU MPFR is licensed under the following license:
```
Copyright 1991, 1993-2020 Free Software Foundation, Inc.

Permission is granted to copy, distribute and/or modify this document under the terms of the GNU Free Documentation License, Version 1.2 or any later version published by the Free Software Foundation; with no Invariant Sections, with no Front-Cover Texts, and with no Back-Cover Texts. A copy of the license is included in GNU Free Documentation License.

The GNU MPFR Library is free software; you can redistribute it and/or modify it under the terms of the GNU Lesser General Public License as published by the Free Software Foundation; either version 3 of the License, or (at your option) any later version.

The GNU MPFR Library is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License along with the GNU MPFR Library; see the file COPYING.LESSER. If not, see https://www.gnu.org/licenses/ or write to the Free Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301, USA.
```

MPFR-JAVA is licensed under the following license:
```
==============================================================================
The K Release License
==============================================================================
University of Illinois/NCSA
Open Source License

Copyright (c) 2014 University of Illinois at Urbana-Champaign.
All rights reserved.

Developed by:

    K Team

    University of Illinois at Urbana-Champaign
    University Alexandru-Ioan Cuza, Romania
    Runtime Verification, Inc.

    http://kframework.org

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal with the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

    * Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimers.

    * Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimers in the documentation and/or other materials provided with the distribution.

    * Neither the names of the K Team, the University of Illinois at Urbana-Champaign, the University Alexandru-Ioan Cuza, nor the names of its contributors may be used to endorse or promote products derived from this Software without specific prior written permission.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE CONTRIBUTORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS WITH THE SOFTWARE.
```

MPIR is licensed under the following license:
```
Copyright 2000, 2001 Free Software Foundation, Inc.

This file is part of the GNU MP Library.

The GNU MP Library is free software; you can redistribute it and/or modify it under the terms of the GNU Lesser General Public License as published by the Free Software Foundation; either version 2.1 of the License, or (at your option) any later version.

The GNU MP Library is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License along with the GNU MP Library; see the file COPYING.LIB.  If not, write to the Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA. 
```

JavaSMT is licensed under the following license: [Apache License Version 2.0](https://github.com/sosy-lab/java-smt/blob/fix-modulo/LICENSE)

CVC5 is licensed under the following license:
```
cvc5 is copyright (C) 2009-2023 by its authors and contributors (see the file
AUTHORS) and their institutional affiliations.  All rights reserved.

The source code of cvc5 is open and available to students, researchers,
software companies, and everyone else to study, to modify, and to redistribute
original or modified versions; distribution is under the terms of the modified
BSD license (reproduced below).  Please note that cvc5 can be configured
(however, by default it is not) to link against some GPLed libraries, and
therefore the use of these builds may be restricted in non-GPL-compatible
projects.  See below for a discussion of CLN and GLPK (the two GPLed optional
library dependences for cvc5), and how to ensure you have a build that doesn't
link against GPLed libraries.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

1. Redistributions of source code must retain the above copyright
   notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright
   notice, this list of conditions and the following disclaimer in the
   documentation and/or other materials provided with the distribution.

3. Neither the name of the copyright holder nor the names of its
   contributors may be used to endorse or promote products derived from
   this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT OWNERS AND CONTRIBUTORS
''AS IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
OWNERS OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.


-------------------------------------------------------------------------------
 Third-Party Software
-------------------------------------------------------------------------------

The cvc5 source code includes third-party software which has its own copyright
and licensing terms, as described below.

The following file contains third-party software.

  cmake/CodeCoverage.cmake

The copyright and licensing information of this file is in its header.

cvc5 incorporates MiniSat code (see src/prop/minisat),
excluded from the above copyright. See licenses/minisat-LICENSE
for copyright and licensing information.

cvc5 by default links against The GNU Multiple Precision (GMP) Arithmetic
Library, which is licensed under GNU LGPL v3.  See the file
licenses/lgpl-3.0.txt for a copy of that license.  Note that according to the
terms of the LGPL, both cvc5's source, and the combined work (cvc5 linked with
GMP) may (and do) remain under the more permissive modified BSD license.

cvc5 also links against the CaDiCaL library
(https://github.com/arminbiere/cadical), which is licensed under
the MIT license.
See https://raw.githubusercontent.com/arminbiere/cadical/master/LICENSE
for copyright and licensing information.  Linking cvc5 against
this library does not affect the license terms of the cvc5 code.

The implementation of the floating point solver in cvc5 depends on symfpu
(https://github.com/martin-cs/symfpu) written by Martin Brain.
See https://raw.githubusercontent.com/martin-cs/symfpu/CVC4/LICENSE for
copyright and licensing information.

cvc5 optionally links against the following libraries:

  ABC                (https://bitbucket.org/alanmi/abc)
  CryptoMiniSat      (https://github.com/msoos/cryptominisat)
  LibPoly            (https://github.com/SRI-CSL/libpoly)
  libedit            (https://thrysoee.dk/editline)

Linking cvc5 against these libraries does not affect the license terms of the
cvc5 code.  See the respective projects for copyright and licensing
information.


-------------------------------------------------------------------------------
 OPTIONAL GPLv3 libraries
-------------------------------------------------------------------------------

Please be advised that the following libraries are covered under the GPLv3
license.  If you choose to link cvc5 against one of these libraries, the
resulting combined work is also covered under the GPLv3. If you want to make
sure you build a version of cvc5 that uses no GPLed libraries, configure cvc5
with the "--no-gpl" option before building (which is the default).  cvc5 can
then be used in contexts where you want to use cvc5 under the terms of the
(modified) BSD license.  See licenses/gpl-3.0.txt for more information.

cvc5 can be optionally configured to link against CLN, the Class Library for
Numbers, available here:

  http://www.ginac.de/CLN/

cvc5 can be optionally configured to link against glpk-cut-log, a modified
version of GLPK, the GNU Linear Programming Kit, available here:

  https://github.com/timothy-king/glpk-cut-log
```