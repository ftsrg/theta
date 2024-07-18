/*
 *  Copyright 2024 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.algorithm.cegar;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.arg.ARG;
import hu.bme.mit.theta.analysis.utils.ArgVisualizer;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.NullLogger;

/**
 * Counterexample-Guided Abstraction Refinement (CEGAR) loop implementation,
 * that uses an Abstractor to explore the abstract state space and a Refiner to
 * check counterexamples and refine them if needed. It also provides certain
 * statistics about its execution.
 */
public final class ArgCegarChecker {

    private ArgCegarChecker() {
    }

    public static <S extends State, A extends Action, P extends Prec> CegarChecker<S, A, P, ARG<S, A>, Trace<S, A>> create(
            final ArgAbstractor<S, A, P> abstractor, final ArgRefiner<S, A, P> refiner) {
        return create(abstractor, refiner, NullLogger.getInstance());
    }

    public static <S extends State, A extends Action, P extends Prec> CegarChecker<S, A, P, ARG<S, A>, Trace<S, A>> create(
            final ArgAbstractor<S, A, P> abstractor, final ArgRefiner<S, A, P> refiner, final Logger logger) {
        return CegarChecker.create(abstractor, refiner, logger, ArgVisualizer.getDefault());
    }

}
