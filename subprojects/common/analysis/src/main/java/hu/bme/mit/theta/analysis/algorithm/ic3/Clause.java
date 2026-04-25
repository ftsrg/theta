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
package hu.bme.mit.theta.analysis.algorithm.ic3;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Or;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import java.util.Collection;
import java.util.Set;
import java.util.stream.Collectors;

public final class Clause {

    private final Set<Expr<BoolType>> literals;

    private Clause(final Collection<Expr<BoolType>> literals) {
        this.literals = Set.copyOf(checkNotNull(literals));
    }

    public static Clause of(final Collection<Expr<BoolType>> literals) {
        return new Clause(literals);
    }

    public Set<Expr<BoolType>> getLiterals() {
        return literals;
    }

    public Expr<BoolType> toExpr() {
        return Or(literals);
    }

    /** Returns true if {@code other} subsumes this clause, i.e. other.literals ⊆ this.literals. */
    public boolean isSubsumedBy(final Clause other) {
        return this.literals.containsAll(other.literals);
    }

    /** Returns the cube ¬l₁ ∧ ¬l₂ ∧ … that is the negation of this clause. */
    public Cube negate() {
        return Cube.of(literals.stream().map(l -> Not(l)).collect(Collectors.toSet()));
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) return true;
        if (!(obj instanceof Clause that)) return false;
        return literals.equals(that.literals);
    }

    @Override
    public int hashCode() {
        return literals.hashCode();
    }

    @Override
    public String toString() {
        return literals.toString();
    }
}
