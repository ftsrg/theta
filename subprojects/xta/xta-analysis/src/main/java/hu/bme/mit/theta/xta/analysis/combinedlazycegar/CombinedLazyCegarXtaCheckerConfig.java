/*
 *  Copyright 2026 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

package hu.bme.mit.theta.xta.analysis.combinedlazycegar;

import hu.bme.mit.theta.analysis.*;
import hu.bme.mit.theta.analysis.algorithm.Proof;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarChecker;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;

public class CombinedLazyCegarXtaCheckerConfig<
        DPrec extends Prec, CPrec extends Prec, Pr extends Proof, C extends Cex> {

    private final CegarChecker<Prod2Prec<DPrec, CPrec>, Pr, C> cegarChecker;
    private final Prod2Prec<DPrec, CPrec> prec;

    public CombinedLazyCegarXtaCheckerConfig(
            final CegarChecker<Prod2Prec<DPrec, CPrec>, Pr, C> cegarChecker,
            final Prod2Prec<DPrec, CPrec> prec) {
        this.cegarChecker = cegarChecker;
        this.prec = prec;
    }

    public SafetyResult<Pr, C> check() {
        return cegarChecker.check(prec);
    }
}
