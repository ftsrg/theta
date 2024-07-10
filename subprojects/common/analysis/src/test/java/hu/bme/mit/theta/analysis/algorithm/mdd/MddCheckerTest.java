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
package hu.bme.mit.theta.analysis.algorithm.mdd;

import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.symbolic.checker.MddCex;
import hu.bme.mit.theta.analysis.algorithm.symbolic.checker.MddChecker;
import hu.bme.mit.theta.analysis.algorithm.symbolic.checker.MddWitness;
import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntExprs;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.IOException;
import java.util.Arrays;
import java.util.Collection;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.*;
import static hu.bme.mit.theta.core.type.anytype.Exprs.Prime;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

@RunWith(value = Parameterized.class)

public class MddCheckerTest {

    private static final VarDecl<IntType> X = Decls.Var("x", IntType.getInstance());
    private static final VarDecl<IntType> Y = Decls.Var("y", IntType.getInstance());
    private static final VarDecl<IntType> Z = Decls.Var("z", IntType.getInstance());


    @Parameterized.Parameter(value = 0)
    public Expr<BoolType> initExpr;

    @Parameterized.Parameter(value = 1)
    public Expr<BoolType> tranExpr;

    @Parameterized.Parameter(value = 2)
    public Expr<BoolType> propExpr;

    @Parameterized.Parameter(value = 3)
    public boolean safe;

    @Parameterized.Parameter(value = 4)
    public Long stateSpaceSize;

    @Parameterized.Parameters(name = "{index}: {0}, {1}, {2}, {3}, {4}")
    public static Collection<Object[]> data() {
        return Arrays.asList(new Object[][]{

                {Eq(X.getRef(), Int(0)), // x = 0
                        Eq(Prime(X.getRef()), X.getRef()), // x'=x
                        Not(Eq(X.getRef(), Int(5))), // not x = 5
                        true,
                        1L},

                {Eq(X.getRef(), Int(0)),
                        Eq(Prime(X.getRef()), X.getRef()),
                        Not(Eq(X.getRef(), Int(0))),
                        false,
                        1L},

                {Eq(X.getRef(), Int(0)), // x = 0
                        And(Eq(Prime(X.getRef()), Add(X.getRef(), Int(1))), Leq(Prime(X.getRef()), Int(10))), // x' = x + 1 & x' <= 10
                        Not(Eq(X.getRef(), Int(5))),
                        false,
                        11L},

                {Eq(X.getRef(), Int(0)),
                        And(Eq(Prime(X.getRef()), Add(X.getRef(), Int(1))), Leq(Prime(X.getRef()), Int(5))),
                        Not(Eq(X.getRef(), Int(5))),
                        false,
                        6L},

                {Eq(X.getRef(), Int(0)),
                        And(Eq(Prime(X.getRef()), Add(X.getRef(), Int(1))), Leq(Prime(X.getRef()), Int(4))),
                        Not(Eq(X.getRef(), Int(5))),
                        true,
                        5L},

                {And(Eq(X.getRef(), Int(0)), Eq(Y.getRef(), Int(0)), Eq(Z.getRef(), Int(0))),
                        And(And(Eq(Prime(X.getRef()), Add(Y.getRef(), Int(1))), Eq(Prime(Y.getRef()), Add(Z.getRef(), Int(1))), Eq(Prime(Z.getRef()), Add(Z.getRef(), Int(1)))), IntExprs.Lt(Prime(Z.getRef()), Int(10))),
                        Not(Eq(X.getRef(), Int(5))),
                        false,
                        10L},

                {And(Eq(X.getRef(), Int(0)), Eq(Y.getRef(), Int(0)), Eq(Z.getRef(), Int(0))),
                        And(And(Eq(Prime(X.getRef()), Add(Y.getRef(), Int(1))), Eq(Prime(Y.getRef()), Add(Z.getRef(), Int(1))), Eq(Prime(Z.getRef()), Add(Z.getRef(), Int(1)))), IntExprs.Lt(Prime(Z.getRef()), Int(6))),
                        Not(Eq(X.getRef(), Int(5))),
                        false,
                        6L},

                {And(Eq(X.getRef(), Int(0)), Eq(Y.getRef(), Int(0)), Eq(Z.getRef(), Int(0))),
                        And(And(Eq(Prime(X.getRef()), Add(Y.getRef(), Int(1))), Eq(Prime(Y.getRef()), Add(Z.getRef(), Int(1))), Eq(Prime(Z.getRef()), Add(Z.getRef(), Int(1)))), IntExprs.Lt(Prime(Z.getRef()), Int(5))),
                        Not(Eq(X.getRef(), Int(5))),
                        true,
                        5L},

        });
    }

    @Test
    public void test() throws IOException {

        final Logger logger = new ConsoleLogger(Logger.Level.SUBSTEP);

        final MddChecker<ExprAction> checker = MddChecker.create(initExpr, VarIndexingFactory.indexing(0), new ExprAction() {
            @Override
            public Expr<BoolType> toExpr() {
                return tranExpr;
            }

            @Override
            public VarIndexing nextIndexing() {
                return VarIndexingFactory.indexing(1);
            }
        }, propExpr, Z3SolverFactory.getInstance(), logger);
        final SafetyResult<MddWitness, MddCex> status = checker.check(null);
        if (safe) {
            assertTrue(status.isSafe());
        } else {
            assertTrue(status.isUnsafe());
        }
        assertEquals(stateSpaceSize, status.getWitness().size());


    }

}
