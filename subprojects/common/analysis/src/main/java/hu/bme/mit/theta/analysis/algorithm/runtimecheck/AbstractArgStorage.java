/*
 *  Copyright 2023 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.analysis.algorithm.runtimecheck;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgTrace;

/**
 * Used by the {@link ArgCexCheckHandler} to store and check abstract ARGs and Counterexamples and
 * if there is any refinement progress on them The concrete implemented ARG storages might differ in
 * what configurations they support (e.g. refinement methods)
 *
 * @param <S>
 * @param <A>
 */
abstract class AbstractArgStorage<S extends State, A extends Action> {

    abstract <P extends Prec> void setCurrentArg(AbstractArg<S, A, P> arg);

    abstract void addCounterexample(ArgTrace<S, A> cex);

    abstract <P extends Prec> boolean check(ARG<S, A> arg, P prec);

    abstract boolean checkIfCounterexampleNew(ArgTrace<S, A> cex);
}
