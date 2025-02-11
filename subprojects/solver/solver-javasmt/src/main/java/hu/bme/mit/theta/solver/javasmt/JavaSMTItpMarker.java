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
package hu.bme.mit.theta.solver.javasmt;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.solver.ItpMarker;
import hu.bme.mit.theta.solver.Stack;
import hu.bme.mit.theta.solver.impl.StackImpl;
import java.util.Collection;

final class JavaSMTItpMarker<T> implements ItpMarker {

    private final Stack<T> terms;

    public JavaSMTItpMarker() {
        terms = new StackImpl<>();
    }

    public void add(final T term) {
        terms.add(checkNotNull(term));
    }

    public void push() {
        terms.push();
    }

    public void pop(final int n) {
        terms.pop(n);
    }

    public Collection<T> getTerms() {
        return terms.toCollection();
    }
}
