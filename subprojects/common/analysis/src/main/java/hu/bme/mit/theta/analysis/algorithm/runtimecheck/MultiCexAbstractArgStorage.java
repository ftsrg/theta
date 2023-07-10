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

import java.util.LinkedHashSet;
import java.util.Set;

/**
 * CexStorage to be used in configurations, where refinement only starts after every counterexample
 * has been discovered (and the ARG has an empty waitlist) e.g. MULTI_SEQ refinement This class only
 * stores ARG hashes, it does not store counterexample hashes
 */
public class MultiCexAbstractArgStorage<S extends State, A extends Action> extends
        AbstractArgStorage<S, A> {

    private final Set<Integer> argHashes = new LinkedHashSet<>();

    <P extends Prec> void setCurrentArg(AbstractArg<S, A, P> arg) {
        // do nothing - args are only added after they are checked at the end of the iteration
    }

    void addCounterexample(ArgTrace<S, A> cex) {
        // do nothing, as there is full exploration of cexs, so we only need to check the ARGs
    }

    /**
     * Checks, if the given arg is new if yes, adds it to the list (and returns true), so the
     * analysis can continue if no, returns false (which means that the analysis is stuck and should
     * be stopped)
     *
     * @param arg the new arg, which should be checked for recurrence
     * @param <P> precision the current precision, which should be checked for recurrence
     * @return checks true, if the arg did not occur before
     */
    private <P extends Prec> boolean checkIfArgNew(AbstractArg<S, A, P> arg) {
        // this marks the end of the abstraction in the iteration - arg is checked and then added, if it is new
        if (argHashes.contains(arg.hashCode())) {
            return true;
        } else {
            argHashes.add(arg.hashCode());
            return false;
        }
    }

    @Override
    <P extends Prec> boolean check(ARG<S, A> arg, P prec) {
        return checkIfArgNew(new AbstractArg<>(arg, prec));
    }

    @Override
    boolean checkIfCounterexampleNew(ArgTrace<S, A> cex) {
        return true; // always return true
    }


}
