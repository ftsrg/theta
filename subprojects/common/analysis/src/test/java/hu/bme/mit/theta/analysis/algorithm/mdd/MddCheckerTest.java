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
package hu.bme.mit.theta.analysis.algorithm.mdd;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.*;
import static hu.bme.mit.theta.core.type.anytype.Exprs.Prime;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntExprs;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.solver.SolverPool;
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory;
import java.util.Arrays;
import java.util.Collection;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

public class MddCheckerTest {

    private static final VarDecl<IntType> X = Decls.Var("x", IntType.getInstance());
    private static final VarDecl<IntType> Y = Decls.Var("y", IntType.getInstance());
    private static final VarDecl<IntType> Z = Decls.Var("z", IntType.getInstance());
    public Expr<BoolType> initExpr;
    public Expr<BoolType> tranExpr;
    public Expr<BoolType> propExpr;
    public boolean safe;
    public Long stateSpaceSize;

    public static Collection<Object[]> data() {
        return Arrays.asList(
                new Object[][] {
                    {
                        Eq(X.getRef(), Int(0)), // x = 0
                        Eq(Prime(X.getRef()), X.getRef()), // x'=x
                        Not(Eq(X.getRef(), Int(5))), // not x = 5
                        true,
                        1L
                    },
                    {
                        Eq(X.getRef(), Int(0)),
                        Eq(Prime(X.getRef()), X.getRef()),
                        Not(Eq(X.getRef(), Int(0))),
                        false,
                        1L
                    },
                    {
                        Eq(X.getRef(), Int(0)), // x = 0
                        And(
                                Eq(Prime(X.getRef()), Add(X.getRef(), Int(1))),
                                Leq(Prime(X.getRef()), Int(10))), // x' = x + 1 & x' <= 10
                        Not(Eq(X.getRef(), Int(5))),
                        false,
                        11L
                    },
                    {
                        Eq(X.getRef(), Int(0)),
                        And(
                                Eq(Prime(X.getRef()), Add(X.getRef(), Int(1))),
                                Leq(Prime(X.getRef()), Int(5))),
                        Not(Eq(X.getRef(), Int(5))),
                        false,
                        6L
                    },
                    {
                        Eq(X.getRef(), Int(0)),
                        And(
                                Eq(Prime(X.getRef()), Add(X.getRef(), Int(1))),
                                Leq(Prime(X.getRef()), Int(4))),
                        Not(Eq(X.getRef(), Int(5))),
                        true,
                        5L
                    },
                    {
                        And(Eq(X.getRef(), Int(0)), Eq(Y.getRef(), Int(0)), Eq(Z.getRef(), Int(0))),
                        And(
                                And(
                                        Eq(Prime(X.getRef()), Add(Y.getRef(), Int(1))),
                                        Eq(Prime(Y.getRef()), Add(Z.getRef(), Int(1))),
                                        Eq(Prime(Z.getRef()), Add(Z.getRef(), Int(1)))),
                                IntExprs.Lt(Prime(Z.getRef()), Int(10))),
                        Not(Eq(X.getRef(), Int(5))),
                        false,
                        10L
                    },
                    {
                        And(Eq(X.getRef(), Int(0)), Eq(Y.getRef(), Int(0)), Eq(Z.getRef(), Int(0))),
                        And(
                                And(
                                        Eq(Prime(X.getRef()), Add(Y.getRef(), Int(1))),
                                        Eq(Prime(Y.getRef()), Add(Z.getRef(), Int(1))),
                                        Eq(Prime(Z.getRef()), Add(Z.getRef(), Int(1)))),
                                IntExprs.Lt(Prime(Z.getRef()), Int(6))),
                        Not(Eq(X.getRef(), Int(5))),
                        false,
                        6L
                    },
                    {
                        And(Eq(X.getRef(), Int(0)), Eq(Y.getRef(), Int(0)), Eq(Z.getRef(), Int(0))),
                        And(
                                And(
                                        Eq(Prime(X.getRef()), Add(Y.getRef(), Int(1))),
                                        Eq(Prime(Y.getRef()), Add(Z.getRef(), Int(1))),
                                        Eq(Prime(Z.getRef()), Add(Z.getRef(), Int(1)))),
                                IntExprs.Lt(Prime(Z.getRef()), Int(5))),
                        Not(Eq(X.getRef(), Int(5))),
                        true,
                        5L
                    },
                });
    }

    @MethodSource("data")
    @ParameterizedTest(name = "{index}: {0}, {1}, {2}, {3}, {4}")
    public void testBfs(Expr<BoolType> initExpr, Expr<BoolType> tranExpr, Expr<BoolType> propExpr, boolean safe, Long stateSpaceSize) throws Exception {
        initMddCheckerTest(initExpr, tranExpr, propExpr, safe, stateSpaceSize);
        testWithIterationStrategy(MddChecker.IterationStrategy.BFS);
    }

    @MethodSource("data")
    @ParameterizedTest(name = "{index}: {0}, {1}, {2}, {3}, {4}")
    public void testSat(Expr<BoolType> initExpr, Expr<BoolType> tranExpr, Expr<BoolType> propExpr, boolean safe, Long stateSpaceSize) throws Exception {
        initMddCheckerTest(initExpr, tranExpr, propExpr, safe, stateSpaceSize);
        testWithIterationStrategy(MddChecker.IterationStrategy.SAT);
    }

    @MethodSource("data")
    @ParameterizedTest(name = "{index}: {0}, {1}, {2}, {3}, {4}")
    public void testGsat(Expr<BoolType> initExpr, Expr<BoolType> tranExpr, Expr<BoolType> propExpr, boolean safe, Long stateSpaceSize) throws Exception {
        initMddCheckerTest(initExpr, tranExpr, propExpr, safe, stateSpaceSize);
        testWithIterationStrategy(MddChecker.IterationStrategy.GSAT);
    }

    public void testWithIterationStrategy(MddChecker.IterationStrategy iterationStrategy)
            throws Exception {

        final Logger logger = new ConsoleLogger(Logger.Level.SUBSTEP);

        final SafetyResult<MddProof, Trace<ExplState, ExprAction>> status;
        try (var solverPool = new SolverPool(Z3LegacySolverFactory.getInstance())) {
            final var monolithicExpr = new MonolithicExpr(initExpr, tranExpr, propExpr);
            final MddChecker checker =
                    new MddChecker(monolithicExpr, solverPool, logger, iterationStrategy);
            status = checker.check(null);
        }

        if (safe) {
            assertTrue(status.isSafe());
            assertEquals(stateSpaceSize, status.getProof().size());
        } else {
            assertTrue(status.isUnsafe());
            assertTrue(stateSpaceSize >= status.getProof().size());
            assertTrue(status.asUnsafe().getCex().length() >= 0);
        }
    }

    public void initMddCheckerTest(Expr<BoolType> initExpr, Expr<BoolType> tranExpr, Expr<BoolType> propExpr, boolean safe, Long stateSpaceSize) {
        this.initExpr = initExpr;
        this.tranExpr = tranExpr;
        this.propExpr = propExpr;
        this.safe = safe;
        this.stateSpaceSize = stateSpaceSize;
    }
}
