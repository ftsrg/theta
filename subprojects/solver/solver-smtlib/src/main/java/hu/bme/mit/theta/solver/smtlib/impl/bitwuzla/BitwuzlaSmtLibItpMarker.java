/*
 *  Copyright 2026 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.solver.smtlib.impl.bitwuzla;

import hu.bme.mit.theta.solver.Stack;
import hu.bme.mit.theta.solver.impl.StackImpl;
import hu.bme.mit.theta.solver.smtlib.solver.interpolation.SmtLibItpMarker;
import java.util.Collection;

/**
 * Marker that also remembers the SMT-LIB names of its assertions: bitwuzla's {@code
 * (get-interpolant (...))} identifies the A side by assertion name, not by term. The names are kept
 * on a stack of their own so that they follow push/pop exactly like the terms do.
 */
public final class BitwuzlaSmtLibItpMarker extends SmtLibItpMarker {

    private final Stack<String> assertionNames = new StackImpl<>();

    void addAssertionName(final String name) {
        assertionNames.add(name);
    }

    Collection<String> getAssertionNames() {
        return assertionNames.toCollection();
    }

    @Override
    public void push() {
        super.push();
        assertionNames.push();
    }

    @Override
    public void pop(final int n) {
        super.pop(n);
        assertionNames.pop(n);
    }
}
