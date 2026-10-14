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
package hu.bme.mit.theta.vmt.analysis.mdd;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;

/** A JavaSMT prover with unchecked exceptions and a model given as variable name to value. */
public final class FormulaProver {

    private final ProverEnvironment prover;
    private final FormulaProverPool pool;

    FormulaProver(ProverEnvironment prover, FormulaProverPool pool) {
        this.prover = prover;
        this.pool = pool;
    }

    public void push() {
        try {
            prover.push();
        } catch (InterruptedException e) {
            throw interrupted(e);
        }
    }

    public void pop() {
        prover.pop();
    }

    public void add(BooleanFormula formula) {
        try {
            prover.addConstraint(formula);
        } catch (InterruptedException e) {
            throw interrupted(e);
        }
    }

    /** Returns true if the asserted formulas are satisfiable. */
    public boolean check() {
        pool.countCheck();
        try {
            return !prover.isUnsat();
        } catch (SolverException e) {
            throw new IllegalStateException(e);
        } catch (InterruptedException e) {
            throw interrupted(e);
        }
    }

    /**
     * The values of {@code vars} in the model of the last satisfiable {@link #check()}, by variable
     * name. A variable the model leaves undefined is missing from the map.
     */
    public Map<String, Object> model(Collection<FormulaVar> vars) {
        try (Model model = prover.getModel()) {
            final Map<String, Object> values = new HashMap<>();
            for (FormulaVar var : vars) {
                final Object value = model.evaluate(var.formula());
                if (value != null) values.put(var.name(), value);
            }
            return values;
        } catch (SolverException e) {
            throw new IllegalStateException(e);
        }
    }

    void close() {
        prover.close();
    }

    private static RuntimeException interrupted(InterruptedException e) {
        Thread.currentThread().interrupt();
        return new IllegalStateException(e);
    }
}
