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
package hu.bme.mit.theta.formalism.cfa.analysis.initprec;

import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.formalism.cfa.CFA;
import hu.bme.mit.theta.solver.Solver;

/**
 * Common interface for inferring initial precision for CFAs.
 */
public interface CfaInitPrec {
	/**
	 * Creates initial ExplPrec based on a CFA.
	 */
	ExplPrec createExpl(CFA cfa);

	/**
	 * Creates initial PredPrec based on a CFA.
	 */
	PredPrec createPred(CFA cfa, Solver solver);
}
