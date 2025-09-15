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
package hu.bme.mit.theta.analysis.multi;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.expr.refinement.Refutation;
import hu.bme.mit.theta.analysis.expr.refinement.RefutationToPrec;

@SuppressWarnings("java:S119")
public record RefToMultiPrec<
                LPrec extends Prec,
                RPrec extends Prec,
                DataPrec extends Prec,
                R extends Refutation>(
        RefutationToPrec<LPrec, R> leftRefToPrec,
        RefutationToPrec<RPrec, R> rightRefToPrec,
        RefutationToPrec<DataPrec, R> dataRefToPrec)
        implements RefutationToPrec<MultiPrec<LPrec, RPrec, DataPrec>, R> {

    @Override
    public MultiPrec<LPrec, RPrec, DataPrec> toPrec(R refutation, int index) {
        return new MultiPrec<>(
                leftRefToPrec.toPrec(refutation, index),
                rightRefToPrec().toPrec(refutation, index),
                dataRefToPrec().toPrec(refutation, index));
    }

    @Override
    public MultiPrec<LPrec, RPrec, DataPrec> join(
            MultiPrec<LPrec, RPrec, DataPrec> prec1, MultiPrec<LPrec, RPrec, DataPrec> prec2) {
        return new MultiPrec<>(
                leftRefToPrec.join(prec1.leftPrec(), prec2.leftPrec()),
                rightRefToPrec.join(prec1.rightPrec(), prec2.rightPrec()),
                dataRefToPrec.join(prec1.dataPrec(), prec2.dataPrec()));
    }
}
