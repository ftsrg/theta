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
package hu.bme.mit.theta.analysis.algorithm.cegar;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;

/**
 * Common interface for the abstractor component. It can create an initial ARG
 * and check an ARG with a given precision.
 */
public interface Abstractor<S extends State, A extends Action, P extends Prec> {

	/**
	 * Create initial ARG.
	 *
	 * @return
	 */
	ARG<S, A> createArg();

	/**
	 * Check ARG with given precision.
	 * 
	 * @param arg
	 * @param prec
	 * @return
	 */
	AbstractorResult check(ARG<S, A> arg, P prec);

}
