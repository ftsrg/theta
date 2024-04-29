/*
 *  Copyright 2024 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.solver.z3;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.ItpMarker;
import hu.bme.mit.theta.solver.Stack;
import hu.bme.mit.theta.solver.impl.StackImpl;

import java.util.Collection;

import static com.google.common.base.Preconditions.checkNotNull;

final class Z3ItpMarker implements ItpMarker {

    private final Stack<Expr<BoolType>> terms;

    public Z3ItpMarker() {
        terms = new StackImpl<>();
    }

    public void add(final Expr<BoolType> term) {
        terms.add(checkNotNull(term));
    }

    public void push() {
        terms.push();
    }

    public void pop(final int n) {
        terms.pop(n);
    }

    public Collection<Expr<BoolType>> getTerms() {
        return terms.toCollection();
    }

}
