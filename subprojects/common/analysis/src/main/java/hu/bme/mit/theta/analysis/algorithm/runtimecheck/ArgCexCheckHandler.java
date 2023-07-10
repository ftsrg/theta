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
import hu.bme.mit.theta.common.exception.NotSolvableException;

public class ArgCexCheckHandler<S extends State, A extends Action> {
	public static ArgCexCheckHandler instance = new ArgCexCheckHandler();
	private AbstractArgStorage<S, A> abstractArgStorage;

	public void setArgCexCheck(boolean shouldCheck, boolean multiseq) {
		if (shouldCheck) {
			if (multiseq) {
				abstractArgStorage = new MultiCexAbstractArgStorage<S, A>();
			} else {
				abstractArgStorage = new SingleCexAbstractArgStorage<S, A>();
			}
		} else {
			abstractArgStorage = null;
		}
	}

	public boolean checkIfCounterexampleNew(ArgTrace<S, A> cex) {
		if (abstractArgStorage != null) {
			return abstractArgStorage.checkIfCounterexampleNew(cex);
		} else return true;
	}

	public <P extends Prec> void setCurrentArg(AbstractArg<S, A, P> arg) {
		if (abstractArgStorage != null) {
			abstractArgStorage.setCurrentArg(arg);
		}
	}

	public <P extends Prec> void checkAndStop(ARG<S, A> arg, P prec) {
		if (abstractArgStorage != null && abstractArgStorage.check(arg, prec)) {
			throw new NotSolvableException();
		}
	}

	public void addCounterexample(ArgTrace<S, A> cexToConcretize) {
		if (abstractArgStorage != null) {
			abstractArgStorage.addCounterexample(cexToConcretize);
		}
	}
}
