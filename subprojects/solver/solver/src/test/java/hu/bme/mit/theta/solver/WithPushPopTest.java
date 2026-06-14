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

import hu.bme.mit.theta.solver.utils.WithPushPop;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

public class WithPushPopTest {

    @Test
    public void test() {
        final SolverStub solver = new SolverStub();
        Assertions.assertEquals(0, solver.nPush);
        try (WithPushPop wpp = new WithPushPop(solver)) {
            Assertions.assertEquals(1, solver.nPush);
        }
        Assertions.assertEquals(0, solver.nPush);
    }

    @Test
    public void testWithFunc() {
        final SolverStub solver = new SolverStub();
        Assertions.assertEquals(0, solver.nPush);
        testFunc(solver);
        Assertions.assertEquals(0, solver.nPush);
    }

    private void testFunc(final Solver solver) {
        try (WithPushPop wpp = new WithPushPop(solver)) {
            return;
        }
    }
}
