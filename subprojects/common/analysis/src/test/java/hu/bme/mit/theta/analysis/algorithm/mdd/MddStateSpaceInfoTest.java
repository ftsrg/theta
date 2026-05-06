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
package hu.bme.mit.theta.analysis.algorithm.mdd;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static org.junit.jupiter.api.Assertions.assertEquals;

import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.delta.collections.IntStatistics;
import hu.bme.mit.delta.collections.RecursiveIntObjMapView;
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
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.enumtype.EnumType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.solver.SolverPool;
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory;
import java.util.List;
import java.util.stream.Stream;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

@Disabled
public class MddStateSpaceInfoTest {

    private static final VarDecl<IntType> X = Decls.Var("x", IntType.getInstance());
    private static final VarDecl<IntType> Y = Decls.Var("y", IntType.getInstance());

    private static final VarDecl<BoolType> A = Decls.Var("a", BoolType.getInstance());
    private static final VarDecl<BoolType> B = Decls.Var("b", BoolType.getInstance());

    private static final EnumType colorType = EnumType.of("color", List.of("red", "green", "blue"));
    private static final VarDecl<EnumType> C = Decls.Var("c", colorType);
    private static final LitExpr<EnumType> RED = colorType.litFromShortName("red");
    private static final LitExpr<EnumType> GREEN = colorType.litFromShortName("green");
    private static final LitExpr<EnumType> BLUE = colorType.litFromShortName("blue");

    static Stream<Arguments> data() {
        return Stream.of(
                Arguments.of(
                        List.of(X, Y),
                        And(Eq(X.getRef(), Int(0)), Eq(Y.getRef(), Int(0))), // x = 0, y = 0
                        1L),
                Arguments.of(
                        List.of(A, B),
                        Eq(A.getRef(), False()), // a = 0
                        2L),
                Arguments.of(
                        List.of(A, B),
                        Eq(B.getRef(), False()), // y = 0
                        2L),
                Arguments.of(
                        List.of(A, B),
                        True(), // true
                        4L),
                Arguments.of(
                        List.of(X, Y),
                        Or(
                                And(Eq(X.getRef(), Int(0)), Eq(Y.getRef(), Int(0))),
                                And(
                                        Eq(X.getRef(), Int(1)),
                                        Eq(Y.getRef(), Int(1)))), // x = 0, y = 0 or x = 1, y = 1
                        4L),
                Arguments.of(
                        List.of(X, Y),
                        Or(
                                And(Eq(X.getRef(), Int(0)), Eq(Y.getRef(), Int(0))),
                                And(Eq(X.getRef(), Int(1)), Eq(Y.getRef(), Int(1))),
                                And(
                                        Eq(X.getRef(), Int(2)),
                                        Eq(
                                                Y.getRef(),
                                                Int(2)))), // x = 0, y = 0 or x = 1, y = 1 or x
                        // = 2, y = 2
                        9L),
                Arguments.of(List.of(A, C), And(A.getRef(), Eq(C.getRef(), RED)), 1L),
                Arguments.of(List.of(A, C), A.getRef(), 3L),
                Arguments.of(List.of(A, C), True(), 6L),
                Arguments.of(List.of(C, A), True(), 6L));
    }

    @ParameterizedTest
    @MethodSource("data")
    public void test(List<VarDecl<?>> varOrder, Expr<BoolType> stateSpaceExpr, Long expectedSize)
            throws Exception {

        try (final SolverPool solverPool = new SolverPool(Z3LegacySolverFactory.getInstance())) {
            final MddGraph<Expr> mddGraph =
                    JavaMddFactory.getDefault().createMddGraph(ExprLatticeDefinition.forExpr());

            final MddVariableOrder variableOrder =
                    JavaMddFactory.getDefault().createMddVariableOrder(mddGraph);
            varOrder.forEach(
                    v -> {
                        final var domainSize =
                                Math.max(v.getType().getDomainSize().getFiniteSize().intValue(), 0);
                        variableOrder.createOnTop(
                                MddVariableDescriptor.create(v.getConstDecl(0), domainSize));
                    });
            final var signature = variableOrder.getDefaultSetSignature();

            final var stateUnfolded = PathUtils.unfold(stateSpaceExpr, 0);
            final MddHandle stateHandle =
                    signature
                            .getTopVariableHandle()
                            .checkInNode(
                                    MddExpressionTemplate.of(
                                            stateUnfolded, o -> (Decl) o, solverPool));

            final var stateSpaceInfo =
                    new MddStateSpaceInfo(
                            signature.getTopVariableHandle().getVariable().orElseThrow(),
                            stateHandle.getNode());
            final var structuralRepresentation = stateSpaceInfo.toStructuralRepresentation();

            final Long resultSize = calculateSize(structuralRepresentation);

            assertEquals(expectedSize, resultSize);
        }
    }

    private static Long calculateSize(RecursiveIntObjMapView<?> mapView) {
        if (mapView.equals(IntObjMapView.empty())) {
            return 1L;
        } else {
            mapView.defaultValue();
            if (mapView.defaultValue() != null) {
                return null;
            } else {
                Long ret = 0L;
                IntStatistics statistics = mapView.statistics();
                int lowestValue = statistics.lowestValue();
                int highestValue = statistics.highestValue();

                for (int i = lowestValue; i < highestValue + 1; ++i) {
                    Long res = calculateSize((RecursiveIntObjMapView<?>) mapView.get(i));
                    if (res == null) {
                        return null;
                    }

                    ret += res;
                }
                return ret;
            }
        }
    }
}
