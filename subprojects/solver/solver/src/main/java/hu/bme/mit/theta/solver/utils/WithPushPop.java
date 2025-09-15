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
package hu.bme.mit.theta.solver.utils;

import hu.bme.mit.theta.solver.SolverBase;
import java.io.Closeable;

/** A helper class for automatic push and pop for solvers using the try-with-resources statement. */
public class WithPushPop implements Closeable {

    private final SolverBase solver;

    public WithPushPop(final SolverBase solver) {
        this.solver = solver;
        solver.push();
    }

    @Override
    public void close() {
        solver.pop();
    }
}
