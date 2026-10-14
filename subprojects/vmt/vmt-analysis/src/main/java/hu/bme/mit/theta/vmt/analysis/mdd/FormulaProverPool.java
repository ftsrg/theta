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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.List;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;

/**
 * Reuses the provers of one {@link SolverContext}. All formulas of a check must come from this
 * context, and the context is not thread-safe, so a pool serves one thread.
 */
public final class FormulaProverPool implements AutoCloseable {

    private final SolverContext context;
    private final Deque<FormulaProver> available = new ArrayDeque<>();
    private final List<FormulaProver> created = new ArrayList<>();
    private long checkCount = 0;

    public FormulaProverPool(SolverContext context) {
        this.context = context;
    }

    public SolverContext getContext() {
        return context;
    }

    public FormulaProver requestProver() {
        final FormulaProver prover = available.poll();
        if (prover != null) return prover;
        final FormulaProver created =
                new FormulaProver(
                        context.newProverEnvironment(ProverOptions.GENERATE_MODELS), this);
        this.created.add(created);
        return created;
    }

    public void returnProver(FormulaProver prover) {
        available.push(prover);
    }

    void countCheck() {
        checkCount++;
    }

    public long getCheckCount() {
        return checkCount;
    }

    @Override
    public void close() {
        created.forEach(FormulaProver::close);
        created.clear();
        available.clear();
    }
}
