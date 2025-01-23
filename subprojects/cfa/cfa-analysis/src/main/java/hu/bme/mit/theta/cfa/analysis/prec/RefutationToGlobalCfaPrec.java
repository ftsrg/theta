/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.cfa.analysis.prec;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.expr.refinement.Refutation;
import hu.bme.mit.theta.analysis.expr.refinement.RefutationToPrec;
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.cfa.analysis.CfaPrec;

public class RefutationToGlobalCfaPrec<P extends Prec, R extends Refutation>
        implements RefutationToPrec<CfaPrec<P>, R> {
    private final RefutationToPrec<P, R> refToPrec;

    private final CFA.Loc referenceLocation;

    public RefutationToGlobalCfaPrec(RefutationToPrec<P, R> refToPrec, CFA.Loc referenceLocation) {
        this.refToPrec = refToPrec;
        this.referenceLocation = referenceLocation;
    }

    @Override
    public GlobalCfaPrec<P> toPrec(R refutation, int index) {
        P prec = refToPrec.toPrec(refutation, index);
        return GlobalCfaPrec.create(prec);
    }

    @Override
    public GlobalCfaPrec<P> join(CfaPrec<P> prec1, CfaPrec<P> prec2) {
        return GlobalCfaPrec.create(
                refToPrec.join(prec1.getPrec(referenceLocation), prec2.getPrec(referenceLocation)));
    }
}
