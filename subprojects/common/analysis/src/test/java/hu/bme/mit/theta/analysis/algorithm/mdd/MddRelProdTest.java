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

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.*;
import static hu.bme.mit.theta.core.type.anytype.Exprs.Prime;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static org.junit.Assert.assertEquals;

import hu.bme.mit.delta.java.mdd.*;
import hu.bme.mit.delta.mdd.MddInterpreter;
import hu.bme.mit.delta.mdd.MddVariableDescriptor;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.AbstractNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.MddNodeNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode.ExprLatticeDefinition;
import hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode.MddExpressionTemplate;
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.LegacyRelationalProductProvider;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.enumtype.EnumType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.solver.SolverPool;
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory;
import java.util.*;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

@RunWith(value = Parameterized.class)
public class MddRelProdTest {

    private static final VarDecl<IntType> X = Decls.Var("x", IntType.getInstance());
    private static final VarDecl<IntType> Y = Decls.Var("y", IntType.getInstance());

    private static final VarDecl<BoolType> A = Decls.Var("a", BoolType.getInstance());
    private static final VarDecl<BoolType> B = Decls.Var("b", BoolType.getInstance());

    private static final EnumType colorType = EnumType.of("color", List.of("red", "green", "blue"));
    private static final VarDecl<EnumType> C = Decls.Var("c", colorType);
    private static final LitExpr<EnumType> RED = colorType.litFromShortName("red");
    private static final LitExpr<EnumType> GREEN = colorType.litFromShortName("green");
    private static final LitExpr<EnumType> BLUE = colorType.litFromShortName("blue");

    @Parameterized.Parameter(value = 0)
    public List<VarDecl<?>> varOrder;

    @Parameterized.Parameter(value = 1)
    public Expr<BoolType> stateExpr;

    @Parameterized.Parameter(value = 2)
    public Expr<BoolType> transExpr;

    @Parameterized.Parameter(value = 3)
    public Long expectedSize;

    @Parameterized.Parameters(name = "{index}: {0}, {1}, {2}, {3}")
    public static Collection<Object[]> data() {
        return Arrays.asList(
                new Object[][] {
                    {
                        List.of(X, Y),
                        And(Eq(X.getRef(), Int(0)), Eq(Y.getRef(), Int(0))), // x = 0, y = 0
                        And(
                                Eq(Prime(X.getRef()), X.getRef()),
                                Eq(Prime(Y.getRef()), Y.getRef())), // x'=x, y'=y
                        1L
                    },
                    {
                        List.of(X, Y),
                        And(Eq(X.getRef(), Int(0)), Eq(Y.getRef(), Int(0))), // x = 0, y = 0
                        And(
                                Eq(Prime(X.getRef()), Add(X.getRef(), Int(1))),
                                Eq(Prime(Y.getRef()), Y.getRef())), // x'=x + 1, y'=y
                        1L
                    },
                    {
                        List.of(X, Y),
                        Or(
                                And(Eq(X.getRef(), Int(0)), Eq(Y.getRef(), Int(0))),
                                And(
                                        Eq(X.getRef(), Int(1)),
                                        Eq(Y.getRef(), Int(1)))), // x = 0, y = 0 or x = 1, y = 1
                        And(
                                Eq(Prime(X.getRef()), X.getRef()),
                                Eq(Prime(Y.getRef()), Y.getRef())), // x'=x, y'=y
                        2L
                    },
                    {
                        List.of(X, Y),
                        Or(
                                And(Eq(X.getRef(), Int(0)), Eq(Y.getRef(), Int(0))),
                                And(
                                        Eq(X.getRef(), Int(1)),
                                        Eq(Y.getRef(), Int(1)))), // x = 0, y = 0 or x = 1, y = 1
                        And(
                                Eq(Prime(X.getRef()), Add(X.getRef(), Int(1))),
                                Eq(Prime(Y.getRef()), Y.getRef())), // x'=x + 1, y'=y
                        2L
                    },
                    {
                        List.of(X, Y),
                        And(Eq(X.getRef(), Int(0)), Eq(Y.getRef(), Int(0))), // x = 0, y = 0
                        And(
                                Or(
                                        Eq(Prime(X.getRef()), X.getRef()),
                                        Eq(Prime(X.getRef()), Add(X.getRef(), Int(1)))),
                                Or(
                                        Eq(Prime(Y.getRef()), Y.getRef()),
                                        Eq(
                                                Prime(Y.getRef()),
                                                Add(
                                                        Y.getRef(),
                                                        Int(1))))), // (x'=x or x'=x+1), (y'=y
                        // or y'=y+1)
                        4L
                    },

                    // These won't ever be supported
                    //                {List.of(X, Y),
                    //                        Eq(X.getRef(), Int(0)), // x = 0
                    //                        Eq(Prime(X.getRef()), X.getRef()), // x'=x
                    //                        1L},
                    //
                    //                {List.of(X, Y),
                    //                        Eq(X.getRef(), Int(0)), // x = 0, y = 0
                    //                        Eq(Prime(X.getRef()), Add(X.getRef(), Int(1))), //
                    // x'=x + 1, y'=y
                    //                        1L},
                    //
                    //                {List.of(X, Y),
                    //                        And(Eq(X.getRef(), Int(0)), Eq(Y.getRef(), Int(0))),
                    // // x = 0, y = 0
                    //                        True(), // true
                    //                        0L},

                    {
                        List.of(A, B),
                        And(A.getRef(), B.getRef()),
                        And(
                                Eq(A.getRef(), Prime(A.getRef())),
                                Eq(B.getRef(), Prime(B.getRef()))), // a'=a, b'=b
                        1L
                    },
                    {
                        List.of(A, B),
                        And(A.getRef(), B.getRef()),
                        And(
                                Eq(A.getRef(), Prime(A.getRef())),
                                Eq(A.getRef(), Prime(B.getRef()))), // a'=a, b'=a
                        1L
                    },
                    {
                        List.of(A, B),
                        And(A.getRef(), B.getRef()),
                        And(
                                Eq(B.getRef(), Prime(A.getRef())),
                                Eq(B.getRef(), Prime(B.getRef()))), // a'=b, b'=b
                        1L
                    },
                    {
                        List.of(A, B),
                        And(A.getRef(), B.getRef()),
                        Eq(A.getRef(), Prime(A.getRef())), // a'=a
                        2L
                    },
                    {
                        List.of(A, B),
                        And(A.getRef(), B.getRef()),
                        Eq(B.getRef(), Prime(B.getRef())), // b'=b
                        2L
                    },
                    {
                        List.of(A, B),
                        And(A.getRef(), B.getRef()),
                        True(), // true
                        4L
                    },
                    {
                        List.of(A, B),
                        True(),
                        And(
                                Eq(A.getRef(), Prime(A.getRef())),
                                Eq(B.getRef(), Prime(B.getRef()))), // a'=a, b'=b
                        4L
                    },
                    {
                        List.of(A, B),
                        True(),
                        True(), // true
                        4L
                    },
                    {
                        List.of(A, B),
                        True(),
                        And(Prime(A.getRef()), Prime(B.getRef())), // a', b'
                        1L
                    },
                    {
                        List.of(A, B),
                        True(),
                        Prime(A.getRef()), // a'
                        2L
                    },
                    {
                        List.of(A, B),
                        True(),
                        Prime(B.getRef()), // b'
                        2L
                    },
                    {
                        List.of(A, C),
                        And(A.getRef(), Eq(C.getRef(), RED)),
                        And(
                                Eq(A.getRef(), Prime(A.getRef())),
                                Eq(C.getRef(), Prime(C.getRef()))), // a'=a, c'=c
                        1L
                    },
                    {
                        List.of(A, C),
                        And(A.getRef(), Eq(C.getRef(), RED)),
                        Eq(A.getRef(), Prime(A.getRef())), // a'=a
                        3L
                    },
                    {
                        List.of(A, C),
                        And(A.getRef(), Eq(C.getRef(), RED)),
                        And(
                                Eq(A.getRef(), Prime(A.getRef())),
                                Or(
                                        Eq(Prime(C.getRef()), RED),
                                        Eq(Prime(C.getRef()), GREEN),
                                        Eq(Prime(C.getRef()), BLUE))), // a'=a
                        3L
                    },
                    {
                        List.of(A, C),
                        True(),
                        And(
                                Eq(A.getRef(), Prime(A.getRef())),
                                Eq(C.getRef(), Prime(C.getRef()))), // a'=a, c'=c
                        6L
                    },
                    {
                        List.of(A, C),
                        And(A.getRef(), Eq(C.getRef(), RED)),
                        True(), // true
                        6L
                    },
                    {
                        List.of(A, C),
                        True(),
                        True(), // true
                        6L
                    },
                });
    }

    @Test
    public void test() throws Exception {

        try (final SolverPool solverPool = new SolverPool(Z3LegacySolverFactory.getInstance())) {
            final MddGraph<Expr> mddGraph =
                    JavaMddFactory.getDefault().createMddGraph(ExprLatticeDefinition.forExpr());

            final MddVariableOrder stateOrder =
                    JavaMddFactory.getDefault().createMddVariableOrder(mddGraph);
            final MddVariableOrder transOrder =
                    JavaMddFactory.getDefault().createMddVariableOrder(mddGraph);

            varOrder.forEach(
                    v -> {
                        final var domainSize =
                                Math.max(v.getType().getDomainSize().getFiniteSize().intValue(), 0);
                        stateOrder.createOnTop(
                                MddVariableDescriptor.create(v.getConstDecl(0), domainSize));
                        transOrder.createOnTop(
                                MddVariableDescriptor.create(v.getConstDecl(1), domainSize));
                        transOrder.createOnTop(
                                MddVariableDescriptor.create(v.getConstDecl(0), domainSize));
                    });

            final var stateSig = stateOrder.getDefaultSetSignature();
            final var transSig = transOrder.getDefaultSetSignature();

            final var stateUnfolded = PathUtils.unfold(stateExpr, 0);
            final var transUnfolded = PathUtils.unfold(transExpr, 0);

            final MddHandle stateHandle =
                    stateSig.getTopVariableHandle()
                            .checkInNode(
                                    MddExpressionTemplate.of(
                                            stateUnfolded, o -> (Decl) o, solverPool));
            final MddHandle transHandle =
                    transSig.getTopVariableHandle()
                            .checkInNode(
                                    MddExpressionTemplate.of(
                                            transUnfolded, o -> (Decl) o, solverPool));

            final AbstractNextStateDescriptor nextStateDescriptor =
                    MddNodeNextStateDescriptor.of(transHandle);

            final var provider = new LegacyRelationalProductProvider(stateSig.getVariableOrder());
            final var result =
                    provider.compute(
                            stateHandle, nextStateDescriptor, stateSig.getTopVariableHandle());

            final Long resultSize = MddInterpreter.calculateNonzeroCount(result);

            assertEquals(expectedSize, resultSize);
        }
    }
}
