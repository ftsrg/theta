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

package hu.bme.mit.theta.solver.smtlib.impl.cvc4;

import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSolverFactory;

import java.nio.file.Path;

public class CVC4SmtLibSolverFactory extends GenericSmtLibSolverFactory {
	private CVC4SmtLibSolverFactory(Path solverPath, String[] args) {
		super(solverPath, args, true);
	}

	public static CVC4SmtLibSolverFactory create(Path solverPath, String[] args) {
		return new CVC4SmtLibSolverFactory(solverPath, args);
	}

	@Override
	public ItpSolver createItpSolver() {
		throw new UnsupportedOperationException("CVC4 does not support interpolation");
	}
}
