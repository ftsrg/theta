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
package hu.bme.mit.theta.solver;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import java.util.Collection;

class SolverStub implements Solver {

    int nPush;

    public SolverStub() {
        nPush = 0;
    }

    @Override
    public void add(final Expr<BoolType> assertion) {
        // Stub
    }

    @Override
    public SolverStatus check() {
        return null;
    }

    @Override
    public void push() {
        ++nPush;
    }

    @Override
    public void pop(final int n) {
        nPush -= n;
    }

    @Override
    public void reset() {
        // Stub
    }

    @Override
    public SolverStatus getStatus() {
        return null;
    }

    @Override
    public Valuation getModel() {
        return null;
    }

    @Override
    public Collection<Expr<BoolType>> getAssertions() {
        return null;
    }

    @Override
    public void close() {
        // Nothing to close
    }
}
