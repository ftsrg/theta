/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

import static com.google.common.base.Preconditions.checkState;

/**
 * CexStorage to be used in configurations, where refinement starts after each counterexample discovered coutnerexample
 * e.g. not MULTI_SEQ refinement, but SEQ_ITP, UNSAT_CORE, etc.
 */
public class SingleCexAbstractArgStorage<S extends State, A extends Action> extends AbstractArgStorage<S, A> {
	private final Set<Integer> counterexamples = new LinkedHashSet<>();
	private final Set<Integer> argprecs = new LinkedHashSet<>();
	private Integer currentArgHash = null;

	<P extends Prec> void setCurrentArg(AbstractArg<S, A, P> arg) {
		currentArgHash = arg.hashCode();
	}

	void addCounterexample(ArgTrace<S, A> cex) {
		checkState(currentArgHash != null);
		int cexHashCode = cex.hashCode();
		counterexamples.add(cexHashCode);
		argprecs.add(currentArgHash);
	}

	boolean checkIfCounterexampleNew(ArgTrace<S, A> cex) {
		checkState(currentArgHash != null);
		int cexHashCode = cex.hashCode();
		if (argprecs.contains(currentArgHash)) {
			if (counterexamples.contains(cexHashCode)) {
				return false;
			}
		}

		return true;
	}

	@Override
	<P extends Prec> boolean check(ARG<S, A> arg, P prec) {
		return arg.getCexs().noneMatch(this::checkIfCounterexampleNew);
	}

    @Override
    boolean wasCexRefinedBefore(ArgTrace<S, A> cex) {
        return checkIfCounterexampleNew(cex);
    }
}