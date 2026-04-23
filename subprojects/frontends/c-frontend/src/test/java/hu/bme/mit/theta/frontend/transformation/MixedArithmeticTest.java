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
package hu.bme.mit.theta.frontend.transformation;

import static hu.bme.mit.theta.core.decl.Decls.Var;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

import hu.bme.mit.theta.c.frontend.dsl.gen.CLexer;
import hu.bme.mit.theta.c.frontend.dsl.gen.CParser;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.logging.NullLogger;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.bvtype.BvArithShiftRightExpr;
import hu.bme.mit.theta.core.type.bvtype.BvLogicShiftRightExpr;
import hu.bme.mit.theta.core.type.bvtype.BvNotExpr;
import hu.bme.mit.theta.core.type.bvtype.BvOrExpr;
import hu.bme.mit.theta.core.type.bvtype.BvShiftLeftExpr;
import hu.bme.mit.theta.core.type.bvtype.BvToIntExpr;
import hu.bme.mit.theta.core.type.bvtype.IntToBvExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.frontend.ParseContext;
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArithmeticType;
import hu.bme.mit.theta.frontend.transformation.grammar.expression.ExpressionVisitor;
import hu.bme.mit.theta.frontend.transformation.grammar.type.DeclarationVisitor;
import hu.bme.mit.theta.frontend.transformation.model.declaration.CDeclaration;
import hu.bme.mit.theta.frontend.transformation.model.statements.CAssignment;
import hu.bme.mit.theta.frontend.transformation.model.statements.CExpr;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.CInteger;
import java.util.ArrayDeque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import org.antlr.v4.runtime.BailErrorStrategy;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.junit.jupiter.api.Test;

public class MixedArithmeticTest {

    @Test
    public void mixedBitwiseOrExpressionUsesLocalBvIsland() {
        final var harness = Harness.of(Map.of("x", signedInt(), "y", signedInt()));

        final Expr<?> expr = harness.parseExpr("x | y");

        assertInstanceOf(IntType.class, expr.getType());
        assertEquals(signedInt().getClass(), CComplexType.getType(expr, harness.parseContext).getClass());
        assertTrue(containsNode(expr, BvOrExpr.class));
        assertTrue(containsNode(expr, IntToBvExpr.class));
        assertTrue(containsNode(expr, BvToIntExpr.class));
    }

    @Test
    public void mixedUnaryNotUsesLocalBvIsland() {
        final var harness = Harness.of(Map.of("x", signedInt()));

        final Expr<?> expr = harness.parseExpr("~x");

        assertInstanceOf(IntType.class, expr.getType());
        assertTrue(containsNode(expr, BvNotExpr.class));
        assertTrue(containsNode(expr, IntToBvExpr.class));
        assertTrue(containsNode(expr, BvToIntExpr.class));
    }

    @Test
    public void mixedSignedRightShiftUsesArithmeticBvShift() {
        final var harness = Harness.of(Map.of("x", signedInt(), "y", signedInt()));

        final Expr<?> expr = harness.parseExpr("x >> y");

        assertInstanceOf(IntType.class, expr.getType());
        assertTrue(containsNode(expr, BvArithShiftRightExpr.class), expr.toString());
        assertTrue(containsNode(expr, IntToBvExpr.class));
        assertTrue(containsNode(expr, BvToIntExpr.class));
    }

    @Test
    public void mixedUnsignedRightShiftUsesLogicalBvShift() {
        final var harness = Harness.of(Map.of("x", unsignedInt(), "y", unsignedInt()));

        final Expr<?> expr = harness.parseExpr("x >> y");

        assertInstanceOf(IntType.class, expr.getType());
        assertTrue(containsNode(expr, BvLogicShiftRightExpr.class), expr.toString());
        assertTrue(containsNode(expr, IntToBvExpr.class));
        assertTrue(containsNode(expr, BvToIntExpr.class));
    }

    @Test
    public void mixedBitwiseOrAssignmentUsesLocalBvIsland() {
        final var harness = Harness.of(Map.of("x", signedInt(), "y", signedInt()));

        final Expr<?> expr =
                new CAssignment(
                                harness.var("x").getRef(),
                                new CExpr(harness.var("y").getRef(), harness.parseContext),
                                "|=",
                                harness.parseContext)
                        .getrExpression();

        assertInstanceOf(IntType.class, expr.getType());
        assertTrue(containsNode(expr, BvOrExpr.class));
        assertTrue(containsNode(expr, IntToBvExpr.class));
        assertTrue(containsNode(expr, BvToIntExpr.class));
    }

    @Test
    public void mixedLeftShiftAssignmentUsesBvShiftAndReturnsInt() {
        final var harness = Harness.of(Map.of("x", unsignedInt(), "y", unsignedInt()));

        final Expr<?> expr =
                new CAssignment(
                                harness.var("x").getRef(),
                                new CExpr(harness.var("y").getRef(), harness.parseContext),
                                "<<=",
                                harness.parseContext)
                        .getrExpression();

        assertInstanceOf(IntType.class, expr.getType());
        assertTrue(containsNode(expr, BvShiftLeftExpr.class));
        assertTrue(containsNode(expr, IntToBvExpr.class));
        assertTrue(containsNode(expr, BvToIntExpr.class));
    }

    private static boolean containsNode(final Expr<?> expr, final Class<?> clazz) {
        if (clazz.isInstance(expr)) {
            return true;
        }
        for (final Expr<?> op : expr.getOps()) {
            if (containsNode(op, clazz)) {
                return true;
            }
        }
        return false;
    }

    private static CComplexType signedInt() {
        return CComplexType.getSignedInt(new ParseContext());
    }

    private static CComplexType unsignedInt() {
        return CComplexType.getUnsignedInt(new ParseContext());
    }

    private static final class Harness {
        private final ParseContext parseContext;
        private final Map<String, VarDecl<?>> vars;
        private final ExpressionVisitor expressionVisitor;

        private Harness(
                final ParseContext parseContext,
                final Map<String, VarDecl<?>> vars,
                final ExpressionVisitor expressionVisitor) {
            this.parseContext = parseContext;
            this.vars = vars;
            this.expressionVisitor = expressionVisitor;
        }

        private static Harness of(final Map<String, CComplexType> varTypes) {
            final ParseContext parseContext = new ParseContext();
            parseContext.setArithmetic(ArithmeticType.mixed);

            final var variables = new ArrayDeque<Tuple2<String, Map<String, VarDecl<?>>>>();
            final Map<String, VarDecl<?>> scope = new LinkedHashMap<>();
            variables.push(Tuple2.of("", scope));

            for (final var entry : varTypes.entrySet()) {
                final var type = rebindType(entry.getValue(), parseContext);
                final VarDecl<?> varDecl = Var(entry.getKey(), type.getSmtType());
                scope.put(entry.getKey(), varDecl);
                parseContext.getMetadata().create(varDecl.getRef(), "cType", type);
            }

            final var declarationVisitor =
                    new DeclarationVisitor(parseContext, null, NullLogger.getInstance());
            final var expressionVisitor =
                    new ExpressionVisitor(
                            new LinkedHashSet<>(),
                            parseContext,
                            null,
                            variables,
                            new LinkedHashMap<VarDecl<?>, CDeclaration>(),
                            declarationVisitor.getTypedefVisitor(),
                            declarationVisitor.getTypeVisitor(),
                            NullLogger.getInstance());
            return new Harness(parseContext, scope, expressionVisitor);
        }

        private static CComplexType rebindType(
                final CComplexType type, final ParseContext parseContext) {
            if (type instanceof CInteger integerType) {
                return CComplexType.getType(
                        (integerType.isSsigned() ? "signed" : "unsigned") + type.getTypeName(),
                        parseContext);
            }
            return CComplexType.getType(type.getTypeName(), parseContext);
        }

        private VarDecl<?> var(final String name) {
            return vars.get(name);
        }

        private Expr<?> parseExpr(final String text) {
            final var lexer = new CLexer(CharStreams.fromString(text));
            final var parser = new CParser(new CommonTokenStream(lexer));
            parser.setErrorHandler(new BailErrorStrategy());
            return parser.assignmentExpression().accept(expressionVisitor);
        }
    }
}