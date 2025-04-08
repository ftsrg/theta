/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.solver.meta;

import hu.bme.mit.theta.common.OsHelper;
import hu.bme.mit.theta.solver.HornSolver;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.UCSolver;

public final class MetaSolverFactory implements SolverFactory {

    private static final MetaSolverFactory INSTANCE;

    static {

        INSTANCE = new MetaSolverFactory();
    }

    private MetaSolverFactory() {}

    public static MetaSolverFactory getInstance() {
        return INSTANCE;
    }


    @Override
    public Solver createSolver() {

        return new MetaSolver();
    }

    @Override
    public UCSolver createUCSolver() {
        throw new UnsupportedOperationException();
    }

    @Override
    public ItpSolver createItpSolver() {
        return new MetaItpSolver();
    }

    public HornSolver createHornSolver() {
        throw new UnsupportedOperationException();
    }
}
