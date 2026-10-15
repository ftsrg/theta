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
package hu.bme.mit.theta.vmt.analysis;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.IterationStrategy;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.common.logging.NullLogger;
import hu.bme.mit.theta.vmt.VmtModel;
import hu.bme.mit.theta.vmt.VmtParser;
import hu.bme.mit.theta.vmt.analysis.mdd.FormulaMddContext;
import hu.bme.mit.theta.vmt.analysis.mdd.FormulaMddEncoder;
import hu.bme.mit.theta.vmt.analysis.mdd.FormulaMddRepresentation;
import hu.bme.mit.theta.vmt.analysis.mdd.FormulaProverPool;
import hu.bme.mit.theta.vmt.analysis.mdd.FormulaVar;
import hu.bme.mit.theta.vmt.analysis.mdd.VmtMddChecker;
import hu.bme.mit.theta.vmt.analysis.mdd.VmtMddProof;
import hu.bme.mit.theta.vmt.analysis.mdd.VmtTrace;
import java.math.BigInteger;
import java.nio.file.Path;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Stream;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;

public class VmtMddCheckerTest {

    private SolverContext context;
    private FormulaProverPool pool;

    @BeforeEach
    public void setUp() throws Exception {
        context = SolverContextFactory.createSolverContext(Solvers.Z3);
        pool = new FormulaProverPool(context);
    }

    @AfterEach
    public void tearDown() {
        pool.close();
        context.close();
    }

    public static Stream<Arguments> data() {
        final List<Arguments> args = new ArrayList<>();
        for (IterationStrategy strategy : List.of(IterationStrategy.GSAT)) {
            for (FormulaMddRepresentation.LookAhead lookAhead :
                    FormulaMddRepresentation.LookAhead.values()) {
                // model, property index, safe, reachable states, shortest trace length
                args.add(Arguments.of("counter.vmt", 0, true, 6L, -1, strategy, lookAhead));
                args.add(Arguments.of("counter.vmt", 1, false, -1L, 5, strategy, lookAhead));
                args.add(Arguments.of("bvinput.vmt", 0, false, -1L, 3, strategy, lookAhead));
                args.add(Arguments.of("bvinput.vmt", 1, true, 12L, -1, strategy, lookAhead));
                args.add(Arguments.of("bvinput.vmt", 2, true, 12L, -1, strategy, lookAhead));
                args.add(Arguments.of("events.vmt", 0, true, 16L, -1, strategy, lookAhead));
                args.add(Arguments.of("events.vmt", 1, false, -1L, 6, strategy, lookAhead));
                args.add(Arguments.of("nondet.vmt", 0, true, -1L, -1, strategy, lookAhead));
                args.add(Arguments.of("nondet.vmt", 1, false, -1L, 4, strategy, lookAhead));
                // uninterpreted functions: one extra state and step for choosing their values
                args.add(Arguments.of("uf-bool.vmt", 0, true, 5L, -1, strategy, lookAhead));
                args.add(Arguments.of("uf-bool.vmt", 1, false, -1L, 2, strategy, lookAhead));
                args.add(Arguments.of("uf-bitvector.vmt", 0, true, 73L, -1, strategy, lookAhead));
                args.add(Arguments.of("uf-bitvector.vmt", 1, false, -1L, 2, strategy, lookAhead));
            }
        }
        return args.stream();
    }

    private VmtModel load(String file) throws Exception {
        return VmtParser.parse(Path.of("src/test/resources/" + file), context.getFormulaManager());
    }

    @ParameterizedTest(name = "{index}: {0} property {1} with {5} and {6}")
    @MethodSource("data")
    public void test(
            String file,
            int propertyIndex,
            boolean safe,
            long stateSpaceSize,
            int traceLength,
            IterationStrategy strategy,
            FormulaMddRepresentation.LookAhead lookAhead)
            throws Exception {
        final VmtModel model = load(file);
        final var property =
                model.getInvariantProperties().stream()
                        .filter(p -> p.index() == propertyIndex)
                        .findFirst()
                        .orElseThrow();
        final VmtMddChecker checker =
                new VmtMddChecker(
                        model,
                        pool,
                        NullLogger.getInstance(),
                        property,
                        strategy,
                        model.getStateVars(),
                        lookAhead);
        final SafetyResult<VmtMddProof, VmtTrace> result = checker.check(UnitPrec.getInstance());

        assertEquals(safe, result.isSafe());
        if (safe) {
            if (stateSpaceSize >= 0) assertEquals(stateSpaceSize, result.getProof().size());
        } else {
            final VmtTrace trace = result.asUnsafe().getCex();
            // the shortest counterexample has this length; the search may return a longer one
            assertTrue(trace.length() >= traceLength, "trace too short: " + trace.length());
            assertTraceIsRealRun(model, trace, property.formula());
        }
    }

    /** Replays the trace on the model: init, every step and the final violation must hold. */
    private void assertTraceIsRealRun(VmtModel model, VmtTrace trace, BooleanFormula property)
            throws Exception {
        final FormulaManager fmgr = model.getFormulaManager();
        final BooleanFormulaManager bmgr = fmgr.getBooleanFormulaManager();
        final List<Map<String, Object>> states = trace.states();
        assertEquals(trace.length() + 1, states.size());

        assertTrue(isSat(bmgr.and(model.getInit(), stateConstraint(model, states.get(0), false))));
        for (int i = 0; i < trace.length(); i++) {
            final int transition = trace.transitions().get(i);
            assertTrue(transition >= 0, "the fired transition was not identified");
            assertTrue(
                    isSat(
                            bmgr.and(
                                    model.getTransSplit().get(transition),
                                    stateConstraint(model, states.get(i), false),
                                    stateConstraint(model, states.get(i + 1), true))),
                    "step " + i + " is not a transition");
        }
        assertTrue(
                isSat(
                        bmgr.and(
                                bmgr.not(property),
                                stateConstraint(model, states.get(states.size() - 1), false))));
    }

    private BooleanFormula stateConstraint(
            VmtModel model, Map<String, Object> values, boolean next) {
        final FormulaManager fmgr = model.getFormulaManager();
        final BooleanFormulaManager bmgr = fmgr.getBooleanFormulaManager();
        final List<BooleanFormula> constraints = new ArrayList<>();
        for (var v : model.getStateVars()) {
            final Object value = values.get(v.name());
            if (value == null) continue;
            final Formula var = next ? v.next() : v.current();
            if (v.type().isBooleanType()) {
                constraints.add(
                        bmgr.equivalence((BooleanFormula) var, bmgr.makeBoolean((Boolean) value)));
            } else if (v.type().isIntegerType()) {
                final var imgr = fmgr.getIntegerFormulaManager();
                constraints.add(
                        imgr.equal(
                                (org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula) var,
                                imgr.makeNumber((BigInteger) value)));
            } else {
                final var bvmgr = fmgr.getBitvectorFormulaManager();
                final var bv = (org.sosy_lab.java_smt.api.BitvectorFormula) var;
                constraints.add(
                        bvmgr.equal(
                                bv, bvmgr.makeBitvector(bvmgr.getLength(bv), (BigInteger) value)));
            }
        }
        return bmgr.and(constraints);
    }

    private boolean isSat(BooleanFormula formula) throws Exception {
        try (ProverEnvironment prover = context.newProverEnvironment()) {
            prover.addConstraint(formula);
            return !prover.isUnsat();
        }
    }

    @ParameterizedTest(name = "{0}")
    @MethodSource("models")
    public void testStateSpaceMatchesExplicitSearch(String file) throws Exception {
        final VmtModel model = load(file);
        final var result =
                new VmtMddChecker(model, pool, NullLogger.getInstance(), null)
                        .check(UnitPrec.getInstance());
        assertTrue(result.isSafe());
        assertEquals(explicitStateCount(model), result.getProof().size());
    }

    public static Stream<String> models() {
        return Stream.of(
                "counter.vmt",
                "bvinput.vmt",
                "events.vmt",
                "nondet.vmt",
                "negated-identity.vmt",
                "uf-bool.vmt",
                "uf-bitvector.vmt");
    }

    /** Breadth-first search over concrete states, with successors enumerated by the solver. */
    private long explicitStateCount(VmtModel model) throws Exception {
        final BooleanFormulaManager bmgr = model.getFormulaManager().getBooleanFormulaManager();
        final Set<Map<String, Object>> seen = new HashSet<>(allSat(model, model.getInit(), false));
        final Deque<Map<String, Object>> frontier = new ArrayDeque<>(seen);
        while (!frontier.isEmpty()) {
            final Map<String, Object> state = frontier.poll();
            final BooleanFormula successors =
                    bmgr.and(model.getTrans(), stateConstraint(model, state, false));
            for (Map<String, Object> successor : allSat(model, successors, true)) {
                if (seen.add(successor)) frontier.add(successor);
            }
        }
        return seen.size();
    }

    /** All assignments of the (current or next) state variables that satisfy the formula. */
    private List<Map<String, Object>> allSat(VmtModel model, BooleanFormula formula, boolean next)
            throws Exception {
        final BooleanFormulaManager bmgr = model.getFormulaManager().getBooleanFormulaManager();
        final List<Map<String, Object>> result = new ArrayList<>();
        try (ProverEnvironment prover =
                context.newProverEnvironment(SolverContext.ProverOptions.GENERATE_MODELS)) {
            prover.addConstraint(formula);
            while (!prover.isUnsat()) {
                final Map<String, Object> values = new HashMap<>();
                try (Model m = prover.getModel()) {
                    for (var v : model.getStateVars()) {
                        final Object value = m.evaluate(next ? v.next() : v.current());
                        assertTrue(value != null, v.name() + " is unconstrained");
                        values.put(v.name(), value);
                    }
                }
                result.add(values);
                prover.addConstraint(bmgr.not(stateConstraint(model, values, next)));
            }
        }
        return result;
    }

    @ParameterizedTest(name = "{0}")
    @MethodSource("models")
    public void testEncodingsAreExact(String file) throws Exception {
        final VmtModel model = load(file);
        final var result =
                new VmtMddChecker(model, pool, NullLogger.getInstance(), null)
                        .check(UnitPrec.getInstance());
        final List<FormulaVar> vars = new ArrayList<>();
        for (var v : model.getStateVars()) {
            vars.add(new FormulaVar(v.name(), v.current(), v.type(), false));
        }
        final FormulaMddEncoder encoder =
                new FormulaMddContext(model.getFormulaManager(), pool, vars).getEncoder();
        final var stateSpace = result.getProof().getMdd();
        final long expected = result.getProof().size();
        assertEquals(expected, allSat(model, encoder.nodeLevel(stateSpace), false).size());
        assertEquals(expected, allSat(model, encoder.vectorLevel(stateSpace), false).size());
    }

    @Test
    public void testLivenessPropertyRejected() throws Exception {
        final VmtModel model = load("events.vmt");
        final var live = model.getProperties().get(2);
        assertThrows(
                IllegalArgumentException.class,
                () ->
                        new VmtMddChecker(model, pool, NullLogger.getInstance(), live)
                                .check(UnitPrec.getInstance()));
    }

    @Test
    public void testNoPropertyExploresAll() throws Exception {
        final VmtModel model = load("events.vmt");
        final var result =
                new VmtMddChecker(model, pool, NullLogger.getInstance(), null)
                        .check(UnitPrec.getInstance());
        assertTrue(result.isSafe());
        assertEquals(16L, result.getProof().size());
    }
}
