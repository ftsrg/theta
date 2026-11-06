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
package hu.bme.mit.theta.solver.validator;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.SolverManager;
import hu.bme.mit.theta.solver.SolverStatus;
import java.util.Collection;

/**
 * Checks the answers of a solver: a SAT answer by evaluating every assertion over the model, and --
 * if an {@code unsatReference} solver is given -- an UNSAT answer by asking that (independent)
 * solver the same question. A disagreement is a {@link SolverValidationException}, never a silently
 * wrong answer.
 */
public class SolverValidatorWrapper implements Solver {
    private final Solver solver;
    private final SolverFactory unsatReference;

    SolverValidatorWrapper(String solver) throws Exception {
        this(SolverManager.resolveSolverFactory(solver).createSolver(), null);
    }

    SolverValidatorWrapper(Solver solver, SolverFactory unsatReference) {
        this.solver = solver;
        this.unsatReference = unsatReference;
    }

    @Override
    public void add(Expr<BoolType> assertion) {
        solver.add(assertion);
    }

    @Override
    public SolverStatus check() {
        SolverStatus check = solver.check();
        if (check.isSat()) {
            final Valuation model = solver.getModel();
            for (Expr<BoolType> assertion : solver.getAssertions()) {
                if (!assertion.eval(model).equals(True())) {
                    throw new SolverValidationException(
                            "Solver problem: " + assertion + " not True over {" + model + "}");
                }
            }
        } else if (check.isUnsat() && unsatReference != null) {
            try (Solver reference = unsatReference.createSolver()) {
                solver.getAssertions().forEach(reference::add);
                if (reference.check().isSat()) {
                    throw new SolverValidationException(
                            "Solver problem: UNSAT, but the reference solver found a model: {"
                                    + reference.getModel()
                                    + "}");
                }
            } catch (SolverValidationException e) {
                throw e;
            } catch (Exception e) {
                throw new RuntimeException("Reference solver failed", e);
            }
        }
        return check;
    }

    @Override
    public void push() {
        solver.push();
    }

    @Override
    public void pop(int n) {
        solver.pop(n);
    }

    @Override
    public void reset() {
        solver.reset();
    }

    @Override
    public SolverStatus getStatus() {
        return solver.getStatus();
    }

    @Override
    public Valuation getModel() {
        return solver.getModel();
    }

    @Override
    public Collection<Expr<BoolType>> getAssertions() {
        return solver.getAssertions();
    }

    @Override
    public void close() throws Exception {
        solver.close();
    }
}
