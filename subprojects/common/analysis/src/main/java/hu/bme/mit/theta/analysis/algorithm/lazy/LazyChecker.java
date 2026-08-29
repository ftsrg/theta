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

package hu.bme.mit.theta.analysis.algorithm.lazy;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.arg.ARG;
import hu.bme.mit.theta.analysis.expr.ExprState;

public class LazyChecker<
                SConcr extends State,
                SAbstr extends State,
                FSConcr extends State,
                FSAbstr extends ExprState,
                A extends Action,
                P extends Prec>
        implements SafetyChecker<
                ARG<LazyState<FSConcr, FSAbstr>, A>, Trace<LazyState<FSConcr, FSAbstr>, A>, P> {

    private final LazyAbstractor<SConcr, SAbstr, FSConcr, FSAbstr, A, P> lazyAbstractor;
    private final ARG<LazyState<FSConcr, FSAbstr>, A> arg;

    private LazyChecker(
            final LazyAbstractor<SConcr, SAbstr, FSConcr, FSAbstr, A, P> lazyAbstractor) {
        this.lazyAbstractor = lazyAbstractor;
        this.arg = lazyAbstractor.createProof();
    }

    public static <
                    SConcr extends State,
                    SAbstr extends State,
                    FSConcr extends State,
                    FSAbstr extends ExprState,
                    A extends Action,
                    P extends Prec>
            LazyChecker<SConcr, SAbstr, FSConcr, FSAbstr, A, P> create(
                    final LazyAbstractor<SConcr, SAbstr, FSConcr, FSAbstr, A, P> lazyAbstractor) {
        return new LazyChecker<>(lazyAbstractor);
    }

    @Override
    public SafetyResult<ARG<LazyState<FSConcr, FSAbstr>, A>, Trace<LazyState<FSConcr, FSAbstr>, A>>
            check(P input) {
        final LazyAbstractorResult result = lazyAbstractor.check(arg, input);
        final LazyStatistics stats = result.getStats();
        if (result.isSafe()) {
            return SafetyResult.safe(arg, stats);
        } else if (result.isUnsafe()) {
            final Trace<LazyState<FSConcr, FSAbstr>, A> cex =
                    arg.getCexs().findFirst().get().toTrace();
            return SafetyResult.unsafe(cex, arg, stats);
        } else {
            throw new AssertionError();
        }
    }
}
