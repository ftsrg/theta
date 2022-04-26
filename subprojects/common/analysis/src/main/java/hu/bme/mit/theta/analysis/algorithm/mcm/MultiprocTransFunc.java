/*
 *  Copyright 2017 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.algorithm.mcm;

import hu.bme.mit.theta.analysis.*;

import java.util.Collection;
import java.util.Map;

public class MultiprocTransFunc<S extends State, A extends Action, P extends Prec> {
	private final Map<Integer, TransFunc<S, A, P>> transFuncMap;

	public MultiprocTransFunc(final Map<Integer, TransFunc<S, A, P>> transFuncMap) {
		this.transFuncMap = transFuncMap;
	}

	public Collection<? extends S> getSuccStates(final int pid, final S state, final A action, final P prec) {
		if(transFuncMap.containsKey(pid)) return transFuncMap.get(pid).getSuccStates(state, action, prec);
		else throw new RuntimeException("No such process: " + pid + ". Known processes: " + transFuncMap.keySet());
	}

}
