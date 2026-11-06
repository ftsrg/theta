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
package org.sosy_lab.java_smt.solvers.yices2;

import static com.google.common.base.Preconditions.checkState;

import com.sri.yices.Config;
import com.sri.yices.Context;
import com.sri.yices.Parameters;
import java.lang.reflect.Field;
import java.util.Collection;
import java.util.Set;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

/**
 * A Yices prover whose context runs in {@code push-pop} mode, as JavaSMT 5 opened it. JavaSMT 6
 * opens every Yices context in {@code interactive} mode, which made the OC checks on libvsync and
 * pthread-complex time out where they used to finish in a few minutes. It lives in JavaSMT's
 * package because the context factory method it overrides is package-private.
 *
 * <p>Checks also use the search parameters Yices tunes for the context, as JavaSMT 5 did by passing
 * none. JavaSMT 6 passes a fresh parameter record, which holds the generic defaults: that alone
 * made the OC checks on workstealqueue_mutex-2 about 1.6 times slower.
 */
public final class PushPopYices2Prover extends Yices2Prover {

    private Parameters params;

    private PushPopYices2Prover(
            Yices2FormulaCreator creator,
            Set<ProverOptions> options,
            BooleanFormulaManager bfmgr,
            ShutdownNotifier shutdownNotifier,
            String solverType) {
        super(creator, options, bfmgr, shutdownNotifier, solverType);
    }

    /** A push-pop prover on {@code context}, or null if it is not a Yices context. */
    public static ProverEnvironment create(SolverContext context, Set<ProverOptions> options) {
        if (!(context instanceof Yices2SolverContext yices)) {
            return null;
        }
        final Object parameters = field(Yices2SolverContext.class, yices, "parameters");
        return new PushPopYices2Prover(
                (Yices2FormulaCreator) field(Yices2SolverContext.class, yices, "creator"),
                options,
                (BooleanFormulaManager) field(Yices2SolverContext.class, yices, "bfmgr"),
                (ShutdownNotifier) field(Yices2SolverContext.class, yices, "shutdownManager"),
                (String) field(parameters.getClass(), parameters, "solverType"));
    }

    @Override
    protected boolean isUnsatImpl() throws SolverException, InterruptedException {
        if (generateUnsatCores) {
            return super.isUnsatImpl();
        }
        final boolean unsat =
                !satCheckWithShutdownNotifier(
                        () -> curEnv.check(params()), curEnv, shutdownNotifier);
        if (unsat
                && (int) field(Yices2AbstractProver.class, this, "stackSizeToUnsat")
                        == Integer.MAX_VALUE) {
            setField(Yices2AbstractProver.class, this, "stackSizeToUnsat", size());
        }
        return unsat;
    }

    @Override
    public boolean isUnsatWithAssumptions(Collection<BooleanFormula> assumptions)
            throws SolverException, InterruptedException {
        checkState(!closed);
        changedSinceLastSatQuery = false;
        wasLastSatCheckSatisfiable = false;
        final int[] terms = new int[assumptions.size()];
        int i = 0;
        for (BooleanFormula f : assumptions) {
            terms[i++] = creator.extractInfo(f);
        }
        final boolean unsat =
                !satCheckWithShutdownNotifier(
                        () -> curEnv.checkWithAssumptions(params(), terms),
                        curEnv,
                        shutdownNotifier);
        if (!unsat) {
            wasLastSatCheckSatisfiable = true;
        }
        return unsat;
    }

    /** The search parameters Yices tunes for this context, the ones a null record selects. */
    private Parameters params() {
        if (params == null) {
            params = new Parameters();
            params.defaultsForContext(curEnv);
        }
        return params;
    }

    @Override
    public void close() {
        if (params != null) {
            params.close();
            params = null;
        }
        super.close();
    }

    private static void setField(Class<?> owner, Object object, String name, Object value) {
        try {
            final Field field = owner.getDeclaredField(name);
            field.setAccessible(true);
            field.set(object, value);
        } catch (ReflectiveOperationException e) {
            throw new IllegalStateException("Unexpected JavaSMT Yices2AbstractProver layout", e);
        }
    }

    private static Object field(Class<?> owner, Object object, String name) {
        try {
            final Field field = owner.getDeclaredField(name);
            field.setAccessible(true);
            return field.get(object);
        } catch (ReflectiveOperationException e) {
            throw new IllegalStateException("Unexpected JavaSMT Yices2 layout", e);
        }
    }

    @Override
    Context newContext(String solverType) {
        final Config config = new Config();
        try {
            config.set("solver-type", solverType);
            config.set("mode", "push-pop");
            return new Context(config);
        } finally {
            config.close();
        }
    }
}
