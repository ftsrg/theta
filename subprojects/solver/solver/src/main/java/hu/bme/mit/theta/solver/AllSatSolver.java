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
package hu.bme.mit.theta.solver;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import java.util.Collection;
import java.util.List;

/**
 * Optional capability: enumerate <em>all</em> satisfying assignments over a chosen set of boolean
 * constants, in one call to the underlying solver.
 *
 * <p>This is what boolean predicate abstraction needs. Without it a client has to emulate the
 * enumeration by repeatedly asking {@code check-sat}, reading a model and asserting its negation,
 * which costs one full solver round trip per model instead of one per abstraction.
 *
 * <p>AllSAT is not part of the SMT-LIB standard, so support is solver specific — the same situation
 * as interpolation, which Theta already exposes through {@link ItpSolver}. Callers must therefore
 * check {@link #supportsAllSat()} and keep a fallback path.
 */
public interface AllSatSolver {

    /** Whether this solver instance can actually answer {@link #allSat}. */
    boolean supportsAllSat();

    /**
     * All distinct assignments to {@code important} that extend to a model of the current
     * assertions. An empty collection means the assertions are unsatisfiable.
     *
     * @throws UnsupportedOperationException if {@link #supportsAllSat()} is false
     */
    Collection<? extends Valuation> allSat(final List<? extends ConstDecl<BoolType>> important);
}
