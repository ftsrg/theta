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

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Add;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.anytype.Exprs.Prime;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static org.junit.Assert.assertEquals;

import hu.bme.mit.delta.java.mdd.JavaMddFactory;
import hu.bme.mit.delta.java.mdd.MddGraph;
import hu.bme.mit.delta.java.mdd.MddHandle;
import hu.bme.mit.delta.java.mdd.MddVariableOrder;
import hu.bme.mit.delta.mdd.MddVariableDescriptor;
import hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode.ExprLatticeDefinition;
import hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode.MddExpressionTemplate;
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.MddStateSpaceInfo;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.enumtype.EnumType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.solver.SolverPool;
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import org.junit.jupiter.api.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

@RunWith(value = Parameterized.class)
public class MddConstrainedCursorTest {

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
    public Expr<BoolType> constraintExpr;

    @Parameterized.Parameter(value = 2)
    public Expr<BoolType> transExpr;

    @Parameterized.Parameter(value = 3)
    public Integer topLevelCursorExpectedSize;

    @Parameterized.Parameters(name = "{index}: {0}, {1}, {2}, {3}")
    public static Collection<Object[]> data() {
        return Arrays.asList(
                new Object[][] {
                    {
                        List.of(X, Y),
                        BoolExprs.And(
                                Eq(X.getRef(), Int(0)), Eq(Y.getRef(), Int(0))), // x = 0, y = 0
                        BoolExprs.And(
                                Eq(Prime(X.getRef()), X.getRef()),
                                Eq(Prime(Y.getRef()), Y.getRef())), // x'=x, y'=y
                        1
                    },
                    {
                        List.of(X, Y),
                        BoolExprs.And(
                                Eq(X.getRef(), Int(0)), Eq(Y.getRef(), Int(0))), // x = 0, y = 0
                        BoolExprs.And(
                                Eq(Prime(X.getRef()), Add(X.getRef(), Int(1))),
                                Eq(Prime(Y.getRef()), Y.getRef())), // x'=x + 1, y'=y
                        1
                    },
                    {
                        List.of(X, Y),
                        Or(
                                BoolExprs.And(Eq(X.getRef(), Int(0)), Eq(Y.getRef(), Int(0))),
                                BoolExprs.And(
                                        Eq(X.getRef(), Int(1)),
                                        Eq(Y.getRef(), Int(1)))), // x = 0, y = 0 or x = 1, y = 1
                        BoolExprs.And(
                                Eq(Prime(X.getRef()), X.getRef()),
                                Eq(Prime(Y.getRef()), Y.getRef())), // x'=x, y'=y
                        2
                    },
                    {
                        List.of(X, Y),
                        BoolExprs.And(
                                Eq(X.getRef(), Int(0)), Eq(Y.getRef(), Int(0))), // x = 0, y = 0
                        BoolExprs.And(
                                Eq(Prime(X.getRef()), Y.getRef()),
                                Eq(Prime(Y.getRef()), Y.getRef())), // x'=y, y'=y
                        1
                    },
                    {
                        List.of(X, Y),
                        BoolExprs.And(
                                Eq(X.getRef(), Int(0)), Eq(Y.getRef(), Int(0))), // x = 0, y = 0
                        BoolExprs.And(
                                Eq(Prime(X.getRef()), Add(Y.getRef(), Int(1))),
                                Eq(Prime(Y.getRef()), Y.getRef())), // x'=y + 1, y'=y
                        1
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

            final var constraintUnfolded = PathUtils.unfold(constraintExpr, 0);
            final var transUnfolded = PathUtils.unfold(transExpr, 0);

            final MddHandle constraintHandle =
                    stateSig.getTopVariableHandle()
                            .checkInNode(
                                    MddExpressionTemplate.of(
                                            constraintUnfolded, o -> (Decl) o, solverPool));
            final MddHandle transHandle =
                    transSig.getTopVariableHandle()
                            .checkInNode(
                                    MddExpressionTemplate.of(
                                            transUnfolded, o -> (Decl) o, solverPool));

            final var stateSpaceInfo =
                    new MddStateSpaceInfo(
                            stateSig.getTopVariableHandle().getVariable().orElseThrow(),
                            constraintHandle.getNode());
            final var structuralRepresentation = stateSpaceInfo.toStructuralRepresentation();
            //            final var structuralHandle =
            // stateSig.getTopVariableHandle().getHandleFor(structuralRepresentation);

            Integer size = 0;
            for (var cursor = transHandle.cursor(structuralRepresentation); cursor.moveNext(); ) {
                size++;
            }

            assertEquals(topLevelCursorExpectedSize, size);
        }
    }
}
