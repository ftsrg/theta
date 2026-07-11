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
package hu.bme.mit.theta.frontend.transformation.grammar.expression;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.*;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Div;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Mod;
import static hu.bme.mit.theta.core.type.anytype.Exprs.Reference;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.FpType;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;
import static hu.bme.mit.theta.frontend.stdlib.MacroExprsKt.fromName;
import static hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType.getSmallestCommonType;

import hu.bme.mit.theta.c.frontend.dsl.gen.CParser;
import hu.bme.mit.theta.c.frontend.dsl.gen.CParser.*;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.Logger.Level;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs;
import hu.bme.mit.theta.core.type.abstracttype.AddExpr;
import hu.bme.mit.theta.core.type.abstracttype.DivExpr;
import hu.bme.mit.theta.core.type.abstracttype.ModExpr;
import hu.bme.mit.theta.core.type.abstracttype.PosExpr;
import hu.bme.mit.theta.core.type.anytype.*;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.bvtype.*;
import hu.bme.mit.theta.core.type.fptype.FpLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.utils.BvUtils;
import hu.bme.mit.theta.core.utils.FpUtils;
import hu.bme.mit.theta.frontend.ParseContext;
import hu.bme.mit.theta.frontend.UnsupportedFrontendElementException;
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig;
import hu.bme.mit.theta.frontend.transformation.grammar.IncludeHandlingCBaseVisitor;
import hu.bme.mit.theta.frontend.transformation.grammar.function.FunctionVisitor;
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.TypedefVisitor;
import hu.bme.mit.theta.frontend.transformation.grammar.type.TypeVisitor;
import hu.bme.mit.theta.frontend.transformation.model.declaration.CDeclaration;
import hu.bme.mit.theta.frontend.transformation.model.declaration.FunctionIds;
import hu.bme.mit.theta.frontend.transformation.model.statements.CAssignment;
import hu.bme.mit.theta.frontend.transformation.model.statements.CCall;
import hu.bme.mit.theta.frontend.transformation.model.statements.CExpr;
import hu.bme.mit.theta.frontend.transformation.model.statements.CStatement;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CVoid;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CStruct;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType;
import java.math.BigInteger;
import java.util.*;
import java.util.function.Function;
import java.util.stream.Collectors;
import org.kframework.mpfr.BigFloat;
import org.kframework.mpfr.BinaryMathContext;

// FunctionVisitor may be null, e.g., when parsing a simple C expression.

public class ExpressionVisitor extends IncludeHandlingCBaseVisitor<Expr<?>> {
    protected final List<CStatement> preStatements = new ArrayList<>();
    protected final List<CStatement> postStatements = new ArrayList<>();
    protected final Deque<Tuple2<String, Map<String, VarDecl<?>>>> variables;
    protected final Set<VarDecl<?>> atomicVars;
    protected final Map<VarDecl<?>, CDeclaration> functions;
    private final ParseContext parseContext;
    private final FunctionVisitor functionVisitor;
    private final TypedefVisitor typedefVisitor;
    private final TypeVisitor typeVisitor;
    private final PostfixVisitor postfixVisitor;
    private final Logger uniqueWarningLogger;

    public ExpressionVisitor(
            Set<VarDecl<?>> atomicVars,
            ParseContext parseContext,
            FunctionVisitor functionVisitor,
            Deque<Tuple2<String, Map<String, VarDecl<?>>>> variables,
            Map<VarDecl<?>, CDeclaration> functions,
            TypedefVisitor typedefVisitor,
            TypeVisitor typeVisitor,
            Logger uniqueWarningLogger) {
        this.atomicVars = atomicVars;
        this.parseContext = parseContext;
        this.functionVisitor = functionVisitor;
        this.variables = variables;
        this.functions = functions;
        this.typedefVisitor = typedefVisitor;
        this.typeVisitor = typeVisitor;
        this.uniqueWarningLogger = uniqueWarningLogger;
        postfixVisitor = new PostfixVisitor();
    }

    protected VarDecl<?> getVar(String name) {
        for (Tuple2<String, Map<String, VarDecl<?>>> variableList : variables) {
            if (variableList.get2().containsKey(name)) {
                VarDecl<?> varDecl = variableList.get2().get(name);
                if (functions.containsKey(varDecl)) {
                    parseContext.getMetadata().create(name, "shouldInline", false);
                }
                return varDecl;
            }
        }
        return null;
    }

    public List<CStatement> getPostStatements() {
        return postStatements;
    }

    public List<CStatement> getPreStatements() {
        return preStatements;
    }

    @Override
    public Expr<?> visitLogicalOrExpression(CParser.LogicalOrExpressionContext ctx) {
        if (ctx.logicalAndExpression().size() > 1) {
            List<Expr<BoolType>> collect =
                    ctx.logicalAndExpression().stream()
                            .map(
                                    logicalAndExpressionContext -> {
                                        Expr<?> expr = logicalAndExpressionContext.accept(this);
                                        return AbstractExprs.Neq(
                                                CComplexType.getType(expr, parseContext)
                                                        .getNullValue(),
                                                expr);
                                    })
                            .collect(Collectors.toList());
            CComplexType signedInt = CComplexType.getSignedInt(parseContext);
            IteExpr<?> ite =
                    Ite(BoolExprs.Or(collect), signedInt.getUnitValue(), signedInt.getNullValue());
            parseContext.getMetadata().create(ite, "cType", signedInt);
            return ite;
        }
        return ctx.logicalAndExpression(0).accept(this);
    }

    @Override
    public Expr<?> visitLogicalAndExpression(CParser.LogicalAndExpressionContext ctx) {
        if (ctx.inclusiveOrExpression().size() > 1) {
            List<Expr<BoolType>> collect =
                    ctx.inclusiveOrExpression().stream()
                            .map(
                                    inclusiveOrExpression -> {
                                        Expr<?> expr = inclusiveOrExpression.accept(this);
                                        return AbstractExprs.Neq(
                                                CComplexType.getType(expr, parseContext)
                                                        .getNullValue(),
                                                expr);
                                    })
                            .collect(Collectors.toList());
            CComplexType signedInt = CComplexType.getSignedInt(parseContext);
            IteExpr<?> ite =
                    Ite(BoolExprs.And(collect), signedInt.getUnitValue(), signedInt.getNullValue());
            parseContext.getMetadata().create(ite, "cType", signedInt);
            return ite;
        }
        return ctx.inclusiveOrExpression(0).accept(this);
    }

    @Override
    public Expr<?> visitInclusiveOrExpression(CParser.InclusiveOrExpressionContext ctx) {
        if (ctx.exclusiveOrExpression().size() > 1) {
            List<Expr<?>> exprs =
                    ctx.exclusiveOrExpression().stream()
                            .map(exclusiveOrExpression -> exclusiveOrExpression.accept(this))
                            .collect(Collectors.toList());
            List<CComplexType> types =
                    exprs.stream()
                            .map((Expr<?> expr1) -> CComplexType.getType(expr1, parseContext))
                            .collect(Collectors.toList());
            CComplexType smallestCommonType = getSmallestCommonType(types, parseContext);
            List<Expr<BvType>> collect =
                    exprs.stream()
                            .map(
                                    expr -> {
                                        Expr<?> ret = smallestCommonType.castTo(expr);
                                        checkState(
                                                ret.getType() instanceof BvType,
                                                "Non-bitvector type found!");
                                        //noinspection unchecked
                                        return (Expr<BvType>) ret;
                                    })
                            .collect(Collectors.toList());
            BvOrExpr or = BvExprs.Or(collect);
            parseContext.getMetadata().create(or, "cType", smallestCommonType);
            return or;
        }
        return ctx.exclusiveOrExpression(0).accept(this);
    }

    @Override
    public Expr<?> visitExclusiveOrExpression(CParser.ExclusiveOrExpressionContext ctx) {
        if (ctx.andExpression().size() > 1) {
            List<Expr<?>> exprs =
                    ctx.andExpression().stream()
                            .map(andExpression -> andExpression.accept(this))
                            .collect(Collectors.toList());
            List<CComplexType> types =
                    exprs.stream()
                            .map((Expr<?> expr1) -> CComplexType.getType(expr1, parseContext))
                            .collect(Collectors.toList());
            CComplexType smallestCommonType = getSmallestCommonType(types, parseContext);
            List<Expr<BvType>> collect =
                    exprs.stream()
                            .map(
                                    expr -> {
                                        Expr<?> ret = smallestCommonType.castTo(expr);
                                        checkState(
                                                ret.getType() instanceof BvType,
                                                "Non-bitvector type found!");
                                        //noinspection unchecked
                                        return (Expr<BvType>) ret;
                                    })
                            .collect(Collectors.toList());
            BvXorExpr xor = BvExprs.Xor(collect);
            parseContext.getMetadata().create(xor, "cType", smallestCommonType);
            return xor;
        }
        return ctx.andExpression(0).accept(this);
    }

    @Override
    public Expr<?> visitAndExpression(CParser.AndExpressionContext ctx) {
        if (ctx.equalityExpression().size() > 1) {
            List<Expr<?>> exprs =
                    ctx.equalityExpression().stream()
                            .map(equalityExpression -> equalityExpression.accept(this))
                            .collect(Collectors.toList());
            List<CComplexType> types =
                    exprs.stream()
                            .map((Expr<?> expr1) -> CComplexType.getType(expr1, parseContext))
                            .collect(Collectors.toList());
            CComplexType smallestCommonType = getSmallestCommonType(types, parseContext);
            List<Expr<BvType>> collect =
                    exprs.stream()
                            .map(
                                    expr -> {
                                        Expr<?> ret = smallestCommonType.castTo(expr);
                                        checkState(
                                                ret.getType() instanceof BvType,
                                                "Non-bitvector type found!");
                                        //noinspection unchecked
                                        return (Expr<BvType>) ret;
                                    })
                            .collect(Collectors.toList());
            BvAndExpr and = BvExprs.And(collect);
            parseContext.getMetadata().create(and, "cType", smallestCommonType);
            return and;
        }
        return ctx.equalityExpression(0).accept(this);
    }

    @Override
    public Expr<?> visitEqualityExpression(CParser.EqualityExpressionContext ctx) {
        if (ctx.relationalExpression().size() > 1) {
            Expr<?> expr = null;
            for (int i = 0; i < ctx.relationalExpression().size() - 1; ++i) {
                Expr<?> leftOp, rightOp;
                if (expr == null) leftOp = ctx.relationalExpression(i).accept(this);
                else leftOp = expr;
                rightOp = ctx.relationalExpression(i + 1).accept(this);
                CComplexType smallestCommonType =
                        getSmallestCommonType(
                                List.of(
                                        CComplexType.getType(leftOp, parseContext),
                                        CComplexType.getType(rightOp, parseContext)),
                                parseContext);
                Expr<?> leftExpr = smallestCommonType.castTo(leftOp);
                Expr<?> rightExpr = smallestCommonType.castTo(rightOp);
                CComplexType signedInt = CComplexType.getSignedInt(parseContext);
                if (ctx.signs.get(i).getText().equals("=="))
                    expr =
                            Ite(
                                    AbstractExprs.Eq(leftExpr, rightExpr),
                                    signedInt.getUnitValue(),
                                    signedInt.getNullValue());
                else
                    expr =
                            Ite(
                                    AbstractExprs.Neq(leftExpr, rightExpr),
                                    signedInt.getUnitValue(),
                                    signedInt.getNullValue());
                parseContext.getMetadata().create(expr, "cType", signedInt);
            }
            return expr;
        }
        return ctx.relationalExpression(0).accept(this);
    }

    @Override
    public Expr<?> visitRelationalExpression(CParser.RelationalExpressionContext ctx) {
        if (ctx.shiftExpression().size() > 1) {
            Expr<?> expr = null;
            for (int i = 0; i < ctx.shiftExpression().size() - 1; ++i) {
                Expr<?> leftOp, rightOp;
                if (expr == null) leftOp = ctx.shiftExpression(i).accept(this);
                else leftOp = expr;
                rightOp = ctx.shiftExpression(i + 1).accept(this);
                CComplexType smallestCommonType =
                        getSmallestCommonType(
                                List.of(
                                        CComplexType.getType(leftOp, parseContext),
                                        CComplexType.getType(rightOp, parseContext)),
                                parseContext);
                Expr<?> leftExpr = smallestCommonType.castTo(leftOp);
                Expr<?> rightExpr = smallestCommonType.castTo(rightOp);
                Expr<BoolType> guard;
                switch (ctx.signs.get(i).getText()) {
                    case "<":
                        guard = AbstractExprs.Lt(leftExpr, rightExpr);
                        break;
                    case ">":
                        guard = AbstractExprs.Gt(leftExpr, rightExpr);
                        break;
                    case "<=":
                        guard = AbstractExprs.Leq(leftExpr, rightExpr);
                        break;
                    case ">=":
                        guard = AbstractExprs.Geq(leftExpr, rightExpr);
                        break;
                    default:
                        throw new UnsupportedFrontendElementException(
                                "Unexpected relational expression sign: "
                                        + ctx.signs.get(i).getText());
                }
                //                MaxEnumAnalyzer.instance.consume(guard); TODO: handle circular
                // dependency
                CComplexType signedInt = CComplexType.getSignedInt(parseContext);
                expr = Ite(guard, signedInt.getUnitValue(), signedInt.getNullValue());
                parseContext.getMetadata().create(expr, "cType", signedInt);
            }
            return expr;
        }
        return ctx.shiftExpression(0).accept(this);
    }

    @Override
    public Expr<?> visitShiftExpression(CParser.ShiftExpressionContext ctx) {
        if (ctx.additiveExpression().size() > 1) {
            Expr<?> accept = ctx.additiveExpression(0).accept(this);
            checkState(accept.getType() instanceof BvType);
            //noinspection unchecked
            Expr<BvType> expr = (Expr<BvType>) accept;
            CComplexType smallestCommonType =
                    getSmallestCommonType(
                            List.of(CComplexType.getType(accept, parseContext)), parseContext);
            checkState(smallestCommonType.getSmtType() instanceof BvType);
            for (int i = 1; i < ctx.additiveExpression().size(); ++i) {
                Expr<BvType> rightOp;
                accept = ctx.additiveExpression(i).accept(this);
                checkState(accept.getType() instanceof BvType);
                //noinspection unchecked
                rightOp = (Expr<BvType>) accept;
                Expr<BvType> leftExpr =
                        cast(
                                smallestCommonType.castTo(expr),
                                (BvType) smallestCommonType.getSmtType());
                Expr<BvType> rightExpr =
                        cast(
                                smallestCommonType.castTo(rightOp),
                                (BvType) smallestCommonType.getSmtType());
                if (ctx.signs.get(i - 1).getText().equals(">>")) {
                    // TODO: is this sound?
                    if (leftExpr.getType().getSigned()) {
                        expr = BvExprs.ArithShiftRight(leftExpr, rightExpr);
                    } else {
                        expr = BvExprs.LogicShiftRight(leftExpr, rightExpr);
                    }
                } else {
                    expr = BvExprs.ShiftLeft(leftExpr, rightExpr);
                }
                parseContext.getMetadata().create(expr, "cType", smallestCommonType);
            }
            return expr;
        }
        return ctx.additiveExpression(0).accept(this);
    }

    @Override
    public Expr<?> visitAdditiveExpression(CParser.AdditiveExpressionContext ctx) {
        if (ctx.multiplicativeExpression().size() > 1) {
            List<Expr<?>> exprs =
                    ctx.multiplicativeExpression().stream()
                            .map(multiplicativeExpression -> multiplicativeExpression.accept(this))
                            .collect(Collectors.toList());
            List<CComplexType> types =
                    exprs.stream()
                            .map((Expr<?> expr1) -> CComplexType.getType(expr1, parseContext))
                            .collect(Collectors.toList());
            CComplexType smallestCommonType = getSmallestCommonType(types, parseContext);
            List<Expr<?>> collect = new ArrayList<>();
            for (int i = 0; i < exprs.size(); i++) {
                parseContext
                        .getMetadata()
                        .create(
                                exprs.get(i),
                                "cType",
                                CComplexType.getType(exprs.get(i), parseContext));
                Expr<?> castTo = smallestCommonType.castTo(exprs.get(i));
                if (i != 0 && ctx.signs.get(i - 1).getText().equals("-")) {
                    castTo = AbstractExprs.Neg(castTo);
                }
                collect.add(castTo);
            }
            Expr<?> add = AbstractExprs.Add(collect);
            parseContext.getMetadata().create(add, "cType", smallestCommonType);
            add = smallestCommonType.castTo(add);
            parseContext.getMetadata().create(add, "cType", smallestCommonType);
            return add;
        }
        return ctx.multiplicativeExpression(0).accept(this);
    }

    @Override
    public Expr<?> visitMultiplicativeExpression(CParser.MultiplicativeExpressionContext ctx) {
        if (ctx.castExpression().size() > 1) {
            Expr<?> expr = null;
            for (int i = 0; i < ctx.castExpression().size() - 1; ++i) {
                Expr<?> leftOp, rightOp;
                if (expr == null) leftOp = ctx.castExpression(i).accept(this);
                else leftOp = expr;
                rightOp = ctx.castExpression(i + 1).accept(this);
                CComplexType smallestCommonType =
                        getSmallestCommonType(
                                List.of(
                                        CComplexType.getType(leftOp, parseContext),
                                        CComplexType.getType(rightOp, parseContext)),
                                parseContext);
                Expr<?> leftExpr = smallestCommonType.castTo(leftOp);
                Expr<?> rightExpr = smallestCommonType.castTo(rightOp);
                switch (ctx.signs.get(i).getText()) {
                    case "*":
                        expr = AbstractExprs.Mul(leftExpr, rightExpr);
                        break;
                    case "/":
                        if (leftExpr.getType() instanceof IntType
                                && rightExpr.getType() instanceof IntType) {
                            expr = createIntDiv(leftExpr, rightExpr);
                            // The division itself is buried inside the Ite that adjusts the solver's
                            // rounding to C's; only that Ite is given a type below. Type the division
                            // too, so that OverflowDetectionPass can find it -- it is the operation
                            // that can overflow (INT_MIN / -1), not the Ite around it.
                            parseContext
                                    .getMetadata()
                                    .create(innerDiv(expr), "cType", smallestCommonType);
                        } else {
                            expr = AbstractExprs.Div(leftExpr, rightExpr);
                        }
                        break;
                    case "%":
                        if (leftExpr.getType() instanceof IntType
                                && rightExpr.getType() instanceof IntType) {
                            expr = createIntMod(leftExpr, rightExpr);
                        } else if (leftExpr.getType() instanceof BvType
                                && rightExpr.getType() instanceof BvType) {
                            expr = AbstractExprs.Rem(leftExpr, rightExpr);
                        } else {
                            expr = AbstractExprs.Mod(leftExpr, rightExpr);
                        }
                        break;
                    default:
                        throw new UnsupportedFrontendElementException(
                                "Unexpected multiplicative expression sign: "
                                        + ctx.signs.get(i).getText());
                }
                parseContext.getMetadata().create(expr, "cType", smallestCommonType);
                expr = smallestCommonType.castTo(expr);
                parseContext.getMetadata().create(expr, "cType", smallestCommonType);
            }
            return expr;
        }
        return ctx.castExpression(0).accept(this);
    }

    /** The {@code Div} that {@link #createIntDiv} wrapped in its rounding-adjustment Ite. */
    private static Expr<?> innerDiv(Expr<?> intDiv) {
        if (intDiv instanceof DivExpr<?>) {
            return intDiv;
        }
        for (Expr<?> op : intDiv.getOps()) {
            Expr<?> found = innerDiv(op);
            if (found != null) {
                return found;
            }
        }
        return null;
    }

    /**
     * Conversion from C (/) semantics to solver (div) semantics.
     *
     * @param a dividend
     * @param b divisor
     * @return expression representing C division semantics with solver operations
     */
    private Expr<?> createIntDiv(Expr<?> a, Expr<?> b) {
        DivExpr<?> aDivB = Div(a, b);
        return Ite(
                Geq(a, Int(0)), // if (a >= 0)
                aDivB, //   a div b
                // else
                Ite(
                        Neq(Mod(a, b), Int(0)), //   if (a mod b != 0)
                        Ite(
                                Geq(b, Int(0)), //     if (b >= 0)
                                Add(aDivB, Int(1)), //       a div b + 1
                                //     else
                                Sub(aDivB, Int(1)) //       a div b - 1
                                ), //   else
                        aDivB //     a div b
                        ));
    }

    /**
     * Conversion from C (%) semantics to solver (mod) semantics.
     *
     * @param a dividend
     * @param b divisor
     * @return expression representing C modulo semantics with solver operations
     */
    private Expr<?> createIntMod(Expr<?> a, Expr<?> b) {
        ModExpr<?> aModB = Mod(a, b);
        return Ite(
                Eq(aModB, Int(0)),
                aModB,
                Ite(
                        Geq(a, Int(0)), // if (a >= 0)
                        aModB, //   a mod b
                        // else
                        Ite(
                                Geq(b, Int(0)), //   if (b >= 0)
                                Sub(aModB, b), //     a mod b - b
                                Add(aModB, b) //     a mod b + b
                                )));
    }

    @Override
    public Expr<?> visitCastExpressionUnaryExpression(
            CParser.CastExpressionUnaryExpressionContext ctx) {
        return ctx.unaryExpression().accept(this);
    }

    @Override
    public Expr<?> visitCastExpressionCast(CParser.CastExpressionCastContext ctx) {
        CComplexType actualType =
                ctx.castDeclarationSpecifierList().accept(typeVisitor).getActualType();
        Expr<?> operand = ctx.castExpression().accept(this);
        if (actualType instanceof CVoid) {
            // `(void)e` only discards e's value; it yields no value of its own, so there is nothing
            // to convert and casting to void is the identity on the expression. Recording `void` as
            // that expression's type would therefore label the *operand* void -- and since a
            // variable's RefExpr is a single shared instance, `(void)x` would make x look void
            // everywhere it is used, breaking every later conversion of it.
            return operand;
        }
        Expr<?> expr = actualType.castTo(operand);
        parseContext.getMetadata().create(expr, "cType", actualType);
        expr = actualType.castTo(expr);
        parseContext.getMetadata().create(expr, "cType", actualType);
        return expr;
    }

    @Override
    public Expr<?> visitUnaryExpressionSizeOrAlignOf(
            CParser.UnaryExpressionSizeOrAlignOfContext ctx) {
        if (ctx.Alignof() != null) {
            uniqueWarningLogger.write(
                    Level.INFO,
                    "WARNING: alignof is not yet implemented, using a literal 0 instead.\n");
            CComplexType signedInt = CComplexType.getSignedInt(parseContext);
            LitExpr<?> zero = signedInt.getNullValue();
            parseContext.getMetadata().create(zero, "cType", signedInt);
            return zero;
        } else if (ctx.typeName() != null) {
            final Optional<CComplexType> type =
                    typedefVisitor
                            .getType(ctx.typeName().getText())
                            .or(
                                    () ->
                                            Optional.ofNullable(
                                                    CComplexType.getType(
                                                            ctx.typeName().getText(),
                                                            parseContext)))
                            .or(
                                    () ->
                                            parseContext
                                                    .getMetadata()
                                                    .getMetadataValue(
                                                            ctx.typeName().getText(),
                                                            "cTypedefName")
                                                    .map(it -> (CComplexType) it))
                            .or(
                                    () ->
                                            Optional.ofNullable(getVar(ctx.typeName().getText()))
                                                    .map(
                                                            v ->
                                                                    CComplexType.getType(
                                                                            v.getRef(),
                                                                            parseContext)))
                            // struct/union/enum tags (e.g. "sizeof(struct node)") aren't typedef
                            // names, builtin keywords, or variables, so none of the lookups above
                            // find them; resolve the tag through the type visitor instead.
                            .or(
                                    () -> {
                                        try {
                                            CSimpleType simpleType =
                                                    ctx.typeName()
                                                            .specifierQualifierList()
                                                            .accept(typeVisitor);
                                            return Optional.ofNullable(simpleType)
                                                    .map(CSimpleType::getActualType);
                                        } catch (RuntimeException e) {
                                            return Optional.empty();
                                        }
                                    });

            if (type.isPresent()) {
                LitExpr<?> value =
                        CComplexType.getSignedInt(parseContext)
                                .getValue("" + Math.max(type.get().width() / 8, 1));
                return value;
            } else {
                uniqueWarningLogger.write(
                        Level.INFO,
                        "WARNING: sizeof got unknown type, using a literal 0 instead.\n");
                CComplexType signedInt = CComplexType.getSignedInt(parseContext);
                LitExpr<?> zero = signedInt.getNullValue();
                parseContext.getMetadata().create(zero, "cType", signedInt);
                return zero;
            }
        } else { // expr != null
            final var expr = ctx.expression().accept(this);
            final var type = CComplexType.getType(expr, parseContext);
            LitExpr<?> value =
                    CComplexType.getSignedInt(parseContext).getValue("" + type.width() / 8);
            return value;
        }
    }

    @Override
    public Expr<?> visitUnaryExpression(CParser.UnaryExpressionContext ctx) {
        Expr<?> ret;
        if (ctx.unaryExpressionSizeOrAlignOf() != null) {
            ret = ctx.unaryExpressionSizeOrAlignOf().accept(this);
        } else {
            ret =
                    ctx.unaryExpressionCast() == null
                            ? ctx.postfixExpression().accept(this)
                            : ctx.unaryExpressionCast().accept(this);
        }
        int increment =
                ctx.unaryExpressionIncrement().size() - ctx.unaryExpressionDecrement().size();
        if (increment != 0) {
            Expr<?> expr = ret;
            CComplexType type = CComplexType.getType(ret, parseContext);
            for (int i = 0; i < Math.abs(increment); i++) {
                if (increment < 0) expr = AbstractExprs.Sub(expr, type.getUnitValue());
                else expr = AbstractExprs.Add(expr, type.getUnitValue());
            }
            parseContext.getMetadata().create(expr, "cType", type);
            expr = type.castTo(expr);
            parseContext.getMetadata().create(expr, "cType", type);
            Expr<?> wrappedExpr = type.castTo(expr);
            CExpr cexpr = new CExpr(wrappedExpr, parseContext);
            CAssignment cAssignment = new CAssignment(ret, cexpr, "=", parseContext);
            preStatements.add(cAssignment);
            if (functionVisitor != null) functionVisitor.recordMetadata(ctx, cAssignment);
            if (functionVisitor != null) functionVisitor.recordMetadata(ctx, cexpr);
        }
        return ret;
    }

    @Override
    public Expr<?> visitUnaryExpressionCast(CParser.UnaryExpressionCastContext ctx) {
        Expr<?> originalOperand = ctx.castExpression().accept(this);
        CComplexType type = CComplexType.getType(originalOperand, parseContext);
        type = getSmallestCommonType(List.of(type), parseContext);
        Expr<?> promotedOperand = type.castTo(originalOperand);
        parseContext.getMetadata().create(promotedOperand, "cType", type);
        switch (ctx.unaryOperator().getText()) {
            case "-":
                {
                    Expr<?> negExpr = AbstractExprs.Neg(promotedOperand);
                    parseContext.getMetadata().create(negExpr, "cType", type);
                    return negExpr;
                }
            case "+":
                return promotedOperand; // no need to update type, it remains the same
            case "!":
                CComplexType signedInt = CComplexType.getSignedInt(parseContext);
                promotedOperand =
                        Ite(
                                Eq(
                                        promotedOperand,
                                        CComplexType.getType(promotedOperand, parseContext)
                                                .getNullValue()),
                                signedInt.getUnitValue(),
                                signedInt.getNullValue());
                parseContext.getMetadata().create(promotedOperand, "cType", signedInt);
                return promotedOperand;
            case "~":
                //noinspection unchecked
                Expr<?> expr = BvExprs.Not(cast(promotedOperand, BvType.of(type.width())));
                parseContext.getMetadata().create(expr, "cType", type);
                return expr;
            case "&":
                // `&f` and `f` denote the same thing for a function: its address (id).
                if (isCallableFunctionPointer(originalOperand)) {
                    return originalOperand;
                }
                checkState(
                        originalOperand instanceof RefExpr<?>
                                || originalOperand instanceof Dereference<?, ?, ?>,
                        "Referencing non-lvalue expressions is not allowed!");
                return reference(originalOperand);
            case "*":
                // `*f` on a function (pointer) is the function itself: (*fp)(x) == fp(x).
                if (isCallableFunctionPointer(originalOperand)) {
                    return originalOperand;
                }
                type = CComplexType.getType(originalOperand, parseContext);
                if (type instanceof CPointer) type = ((CPointer) type).getEmbeddedType();
                else if (type instanceof CArray) type = ((CArray) type).getEmbeddedType();
                // C defines *(p + i) as p[i]. Object sizes are keyed on the base expression, so
                // the index has to become the dereference offset: folding it into the base makes
                // every such access read an unallocated object and look out of bounds.
                Expr<?> base = originalOperand;
                Expr<?> offset = CComplexType.getUnsignedLong(parseContext).getNullValue();
                if (stripPos(originalOperand) instanceof AddExpr<?> addExpr) {
                    final List<Expr<?>> pointerOps = new ArrayList<>();
                    final List<Expr<?>> indexOps = new ArrayList<>();
                    for (Expr<?> rawOp : addExpr.getOps()) {
                        Expr<?> op = stripPos(rawOp);
                        CComplexType opType = CComplexType.getType(op, parseContext);
                        if (opType instanceof CPointer || opType instanceof CArray) {
                            pointerOps.add(op);
                        } else {
                            indexOps.add(op);
                        }
                    }
                    if (pointerOps.size() == 1 && !indexOps.isEmpty()) {
                        base = pointerOps.get(0);
                        offset = indexOps.size() == 1 ? indexOps.get(0) : Add(indexOps);
                    }
                }
                return dereference(base, offset, type);
        }
        return originalOperand;
    }

    /**
     * Removes the identity ("unary plus") casts the frontend wraps around promoted operands, so
     * that the underlying expression -- and the C type recorded for it -- can be inspected.
     */
    private static Expr<?> stripPos(Expr<?> expr) {
        while (expr instanceof PosExpr<?> pos) {
            expr = pos.getOp();
        }
        return expr;
    }

    @SuppressWarnings("unchecked")
    private <T extends Type> Expr<?> dereference(
            Expr<?> accept, Expr<?> offset, CComplexType type) {
        CComplexType ptrType = CComplexType.getType(accept, parseContext);
        Dereference<T, ?, Type> of =
                Exprs.Dereference((Expr<T>) accept, ptrType.castTo(offset), type.getSmtType());
        parseContext.getMetadata().create(of, "cType", type);
        return of;
    }

    private Expr<?> reference(Expr<?> accept) {
        final var newType =
                new CPointer(null, CComplexType.getType(accept, parseContext), parseContext);
        Reference<Type, ?> of = Reference(accept, newType.getSmtType());
        parseContext.getMetadata().create(of, "cType", newType);
        return of;
    }

    @Override
    public Expr<?> visitPostfixExpression(CParser.PostfixExpressionContext ctx) {
        Expr<?> builtin = handleBuiltinCall(ctx);
        if (builtin != null) {
            return builtin;
        }
        registerIfFunctionUsedAsValue(ctx);
        Expr<?> primary = ctx.primaryExpression().accept(this);
        if (primary == null) {
            return null;
        }
        for (PostfixExpressionAccessContext pfExpr : ctx.pfExprs) {
            primary = pfExpr.accept(postfixVisitor).apply(primary);
        }
        return primary;
    }

    /**
     * A function name that is NOT immediately called denotes the function's address (C decays a
     * function designator to a pointer). Registering it here marks the function as address-taken,
     * so that it becomes a candidate for indirect calls and its variable is initialized to its id
     * (see {@code FrontendXcfaBuilder}). The expression itself stays the ordinary reference to the
     * function's variable -- whose value IS the id -- so that consumers such as {@code
     * CLibraryFunctionsPass} (pthread_create's start routine) keep working unchanged.
     */
    private void registerIfFunctionUsedAsValue(CParser.PostfixExpressionContext ctx) {
        if (!(ctx.primaryExpression() instanceof CParser.PrimaryExpressionIdContext idCtx)) {
            return;
        }
        boolean isCalled =
                !ctx.pfExprs.isEmpty() && ctx.pfExprs.get(0).postfixExpressionBraces() != null;
        if (isCalled) {
            return;
        }
        String name = idCtx.Identifier().getText();
        VarDecl<?> variable = getVar(name);
        if (variable != null && functions.containsKey(variable)) {
            FunctionIds.idOf(name);
            parseContext.getMetadata().create(variable.getRef(), "isFunctionPointer", true);
        }
    }

    /**
     * True if this expression denotes a callable function pointer: a variable declared as one, or a
     * function's address taken directly (e.g. {@code (&f)(x)}).
     */
    private boolean isCallableFunctionPointer(Expr<?> expr) {
        if (parseContext.getMetadata().getMetadataValue(expr, "isFunctionPointer").isPresent()) {
            return true;
        }
        // Carried on the type, so that function pointers reached through a struct field, an array
        // element or a typedef are recognized as well.
        return CComplexType.getType(expr, parseContext) instanceof CPointer cPointer
                && cPointer.isFunctionPointer();
    }

    /** Marker call emitted for an indirect call; {@link FunctionPointerCallsPass} expands it. */
    public static final String INDIRECT_CALL = "__theta_indirect_call";

    /**
     * Emits a call through a function pointer as a marker call whose first argument is the pointer
     * itself. A later pass replaces it with a nondeterministic dispatch over the candidate set (the
     * functions whose address is taken).
     */
    private Expr<?> indirectCall(PostfixExpressionBracesContext ctx, Expr<?> functionPointer) {
        FunctionIds.markIndirectCall();
        List<CStatement> arguments = new ArrayList<>();
        arguments.add(new CExpr(functionPointer, parseContext));
        CParser.ArgumentExpressionListContext exprList = ctx.argumentExpressionList();
        if (exprList != null) {
            if (functionVisitor == null) {
                throw new RuntimeException(
                        "Cannot parse function calls without a function visitor.");
            }
            for (AssignmentExpressionContext arg : exprList.assignmentExpression()) {
                arguments.add(arg.accept(functionVisitor));
            }
        }
        // The call returns what the pointed-to function returns, i.e. the pointee of the pointer.
        CComplexType pointerType = CComplexType.getType(functionPointer, parseContext);
        CComplexType returnType =
                pointerType instanceof CPointer cPointer
                        ? cPointer.getEmbeddedType()
                        : CComplexType.getSignedInt(parseContext);
        parseContext.getMetadata().create(INDIRECT_CALL, "cType", returnType);
        CCall cCall = new CCall(INDIRECT_CALL, arguments, parseContext);
        preStatements.add(cCall);
        if (functionVisitor != null) functionVisitor.recordMetadata(ctx, cCall);
        return cCall.getRet().getRef();
    }

    /**
     * Handles the few GCC builtins that are pure value pass-throughs (or trivially constant) and
     * have no declaration to resolve, so that they don't fail as "No such variable or macro". These
     * are compile-time hints with exact, side-effect-free semantics:
     *
     * <ul>
     *   <li>{@code __builtin_expect(exp, c)} and {@code __builtin_expect_with_probability(exp, c,
     *       p)} evaluate to {@code exp};
     *   <li>{@code __builtin_constant_p(exp)} evaluates to {@code 0} (a sound, conservative answer:
     *       "not a compile-time constant").
     * </ul>
     *
     * Also aliases the {@code __builtin_}-prefixed floating-point classification builtins that have
     * no declaration to the plain library names that {@code FpFunctionsToExprsPass} already models
     * exactly ({@code isnan}, {@code isinf}, {@code isfinite}, {@code isnormal}), by emitting a
     * call to the plain name.
     *
     * <p>Returns {@code null} when {@code ctx} is not such a call, so normal handling proceeds.
     */
    private Expr<?> handleBuiltinCall(CParser.PostfixExpressionContext ctx) {
        if (!(ctx.primaryExpression() instanceof CParser.PrimaryExpressionIdContext idCtx)
                || ctx.pfExprs.isEmpty()) {
            return null;
        }
        CParser.PostfixExpressionBracesContext call = ctx.pfExprs.get(0).postfixExpressionBraces();
        if (call == null || ctx.pfExprs.size() != 1) {
            return null;
        }
        String name = idCtx.Identifier().getText();
        List<AssignmentExpressionContext> args =
                call.argumentExpressionList() == null
                        ? List.of()
                        : call.argumentExpressionList().assignmentExpression();
        switch (name) {
            case "__builtin_expect", "__builtin_expect_with_probability" -> {
                if (args.isEmpty()) {
                    return null;
                }
                return args.get(0).accept(this);
            }
            case "__builtin_constant_p" -> {
                CComplexType signedInt = CComplexType.getSignedInt(parseContext);
                LitExpr<?> zero = signedInt.getNullValue();
                parseContext.getMetadata().create(zero, "cType", signedInt);
                return zero;
            }
            case "__builtin_isinf", "__builtin_isinf_sign" -> {
                return callModeledLibraryFunction("isinf", args, false);
            }
            case "__builtin_isnormal" -> {
                return callModeledLibraryFunction("isnormal", args, false);
            }
            case "__builtin_alloca", "__builtin_alloca_with_align" -> {
                return callAlloca(args);
            }
            case "__builtin_uadd_overflow",
                    "__builtin_uaddl_overflow",
                    "__builtin_uaddll_overflow" -> {
                return unsignedOverflowBuiltin(args, true);
            }
            case "__builtin_umul_overflow",
                    "__builtin_umull_overflow",
                    "__builtin_umulll_overflow" -> {
                return unsignedOverflowBuiltin(args, false);
            }
            default -> {
                // The remaining __builtin_ classification/comparison functions have no declaration
                // but are exactly the int-returning library predicates FpFunctionsToExprsPass
                // models; alias them to their plain names. Only allow-listed names are routed, so
                // unmodeled builtins are left to fail loudly rather than being silently havoced.
                // (The value-returning math builtins -- fabs, sqrt, ... -- are intentionally not
                // routed here: without a declaration the synthetic call would default to an int
                // return type and mismatch the fp result.)
                if (name.startsWith("__builtin_")) {
                    String plain = name.substring("__builtin_".length());
                    if (MODELED_INT_LIBRARY_FUNCTIONS.contains(plain)) {
                        return callModeledLibraryFunction(plain, args, false);
                    }
                    if (MODELED_FP_LIBRARY_FUNCTIONS.contains(plain)) {
                        return callModeledLibraryFunction(plain, args, true);
                    }
                }
                return null;
            }
        }
    }

    /**
     * Int-returning library classification/comparison functions that {@code FpFunctionsToExprsPass}
     * models exactly, so their {@code __builtin_}-prefixed (declaration-less) forms can be aliased
     * to them. Only int-returning functions are listed, because a synthetic call to a name with no
     * declaration defaults to an int return type.
     */
    private static final Set<String> MODELED_INT_LIBRARY_FUNCTIONS =
            Set.of(
                    "isnan",
                    "isinf",
                    "isfinite",
                    "isgreater",
                    "isgreaterequal",
                    "isless",
                    "islessequal",
                    "islessgreater",
                    "isunordered");

    /**
     * Value-returning library math functions that {@code FpFunctionsToExprsPass} models exactly.
     * These return the (promoted) type of their first argument, which must be set explicitly on the
     * synthetic call since the {@code __builtin_} form has no declaration to supply it.
     */
    private static final Set<String> MODELED_FP_LIBRARY_FUNCTIONS =
            Set.of(
                    "fabs", "fabsf", "fabsl", "sqrt", "sqrtf", "sqrtl", "floor", "floorf", "floorl",
                    "ceil", "ceilf", "ceill", "trunc", "truncf", "truncl", "round", "roundf",
                    "roundl", "fmin", "fminf", "fminl", "fmax", "fmaxf", "fmaxl", "fmod", "fmodf",
                    "fmodl");

    /**
     * The member's offset within its compound object: its position among the fields for a struct,
     * and 0 for every member of a union, whose members all start at the same address.
     *
     * <p>A member access lowers to {@code __arrays_T[base][offset]} -- an array *per SMT type* --
     * so giving a union's members offset 0 makes two members of the same type genuinely alias, and
     * writing one is read back through the other. That is the case the benchmarks depend on for
     * their verdicts (a union used as "two ways of naming the same data"). Members of *different*
     * types land in different arrays and so cannot alias at all: modelling that faithfully means
     * reinterpreting the object's bits, which needs the flat object layout of AD7. Rather than
     * answer such a program unsoundly, an access to a member of a union whose members do not all
     * share one representation is rejected -- the union may still be declared and passed around,
     * which is all the opaque system-header unions (pthread_mutex_t, mbstate_t) ever need.
     */
    private int memberOffset(CStruct compound, String memberName) {
        if (!compound.isUnion()) {
            return compound.getFields().stream().map(Tuple2::get1).toList().indexOf(memberName);
        }
        CComplexType accessed = compound.getFieldsAsMap().get(memberName);
        if (accessed != null) {
            for (Tuple2<String, CComplexType> field : compound.getFields()) {
                if (!sameRepresentation(accessed, field.get2())) {
                    throw new UnsupportedFrontendElementException(
                            ("Accessing member [%s] of a union whose members do not all share a"
                                            + " representation ([%s] is a %s, [%s] is a %s) would"
                                            + " require bit-level type punning, which is not"
                                            + " supported.")
                                    .formatted(
                                            memberName,
                                            memberName,
                                            accessed.getTypeName(),
                                            field.get1(),
                                            field.get2().getTypeName()));
                }
            }
        }
        return 0;
    }

    /**
     * Whether two union members occupy their shared storage identically, so that writing one and
     * reading the other is exactly the identity.
     *
     * <p>The C type is what decides this, not the SMT type: under integer arithmetic every integer
     * type is modelled by the same unbounded {@code Int}, so an {@code int} and a {@code char}
     * member would compare equal there and silently alias without the truncation C mandates ({@code
     * u.i = 300; u.c} must be 44, not 300).
     */
    private static boolean sameRepresentation(CComplexType a, CComplexType b) {
        return a.getClass().equals(b.getClass()) && a.getSmtType().equals(b.getSmtType());
    }

    /**
     * Emits the `alloca(size)` call that {@code AllocaFunctionPass} lowers into a stack allocation.
     * The {@code __builtin_} form has no declaration, so the pointer return type is supplied here
     * (it would otherwise default to int). {@code __builtin_alloca_with_align} only adds an
     * alignment argument, which does not affect the modelled size, so it is dropped.
     */
    private Expr<?> callAlloca(List<AssignmentExpressionContext> args) {
        if (functionVisitor == null || args.isEmpty()) {
            return null;
        }
        List<CStatement> arguments = new ArrayList<>();
        arguments.add(args.get(0).accept(functionVisitor));
        CComplexType pointerType =
                new CPointer(null, CComplexType.getSignedInt(parseContext), parseContext);
        parseContext.getMetadata().create(ALLOCA, "cType", pointerType);
        CCall cCall = new CCall(ALLOCA, arguments, parseContext);
        preStatements.add(cCall);
        return cCall.getRet().getRef();
    }

    private static final String ALLOCA = "alloca";

    /**
     * Models {@code __builtin_uadd*_overflow(a, b, res)} and {@code __builtin_umul*_overflow}: the
     * wrapped result is stored through {@code res} and the call returns whether the exact result
     * was not representable. Only the unsigned forms are modelled -- they are the ones that occur,
     * and unlike the signed forms their wraparound is defined, so both the result and the overflow
     * condition can be stated in the operand type itself (no widening), which keeps this correct
     * under both integer and bitvector arithmetic:
     *
     * <ul>
     *   <li>addition wraps exactly when the wrapped sum came out below either operand;
     *   <li>multiplication wraps exactly when dividing the wrapped product by one (nonzero) operand
     *       does not give the other back.
     * </ul>
     *
     * <p>The overflow flag is captured into a temporary <em>before</em> the result is stored, so
     * that the model stays correct when {@code res} points at one of the operands.
     */
    private Expr<?> unsignedOverflowBuiltin(
            List<AssignmentExpressionContext> args, boolean isAddition) {
        if (functionVisitor == null || args.size() != 3) {
            return null;
        }
        Expr<?> a = args.get(0).accept(functionVisitor).getExpression();
        Expr<?> b = args.get(1).accept(functionVisitor).getExpression();
        Expr<?> resultPointer = args.get(2).accept(functionVisitor).getExpression();
        if (!(CComplexType.getType(resultPointer, parseContext) instanceof CPointer pointer)) {
            return null;
        }
        CComplexType type = pointer.getEmbeddedType();

        Expr<?> left = typed(type.castTo(a), type);
        Expr<?> right = typed(type.castTo(b), type);
        Expr<?> exact = typed(isAddition ? Add(left, right) : Mul(left, right), type);
        Expr<?> wrapped = typed(type.castTo(exact), type);

        Expr<BoolType> overflowed;
        if (isAddition) {
            overflowed = AbstractExprs.Lt(wrapped, left);
        } else {
            Expr<?> quotient =
                    typed(
                            wrapped.getType() instanceof IntType
                                            && left.getType() instanceof IntType
                                    ? createIntDiv(wrapped, left)
                                    : Div(wrapped, left),
                            type);
            overflowed =
                    BoolExprs.And(
                            BoolExprs.Not(AbstractExprs.Eq(left, type.getNullValue())),
                            BoolExprs.Not(AbstractExprs.Eq(quotient, right)));
        }

        CComplexType signedInt = CComplexType.getSignedInt(parseContext);
        VarDecl<?> flag = functionVisitor.createTempVar(signedInt, "overflow");
        Expr<?> flagValue =
                typed(
                        Ite(overflowed, signedInt.getUnitValue(), signedInt.getNullValue()),
                        signedInt);
        preStatements.add(
                new CAssignment(
                        flag.getRef(), new CExpr(flagValue, parseContext), "=", parseContext));

        Expr<?> target =
                dereference(
                        resultPointer,
                        CComplexType.getUnsignedLong(parseContext).getNullValue(),
                        type);
        preStatements.add(
                new CAssignment(target, new CExpr(wrapped, parseContext), "=", parseContext));
        return flag.getRef();
    }

    private Expr<?> typed(Expr<?> expr, CComplexType type) {
        parseContext.getMetadata().create(expr, "cType", type);
        return expr;
    }

    /**
     * Emits a call to a library function that a later pass ({@code FpFunctionsToExprsPass}) models,
     * mirroring the ordinary call-lowering path. When {@code returnsFirstArgType} is set, the
     * call's return type is set to the first argument's type (value-returning math functions);
     * otherwise it defaults to {@code int} (classification/comparison predicates). Returns {@code
     * null} if calls cannot be built here (no function visitor), so the caller falls back to normal
     * handling.
     */
    private Expr<?> callModeledLibraryFunction(
            String functionName,
            List<AssignmentExpressionContext> args,
            boolean returnsFirstArgType) {
        if (functionVisitor == null || (returnsFirstArgType && args.isEmpty())) {
            return null;
        }
        List<CStatement> arguments = new ArrayList<>();
        for (AssignmentExpressionContext arg : args) {
            arguments.add(arg.accept(functionVisitor));
        }
        if (returnsFirstArgType) {
            CComplexType returnType =
                    CComplexType.getType(arguments.get(0).getExpression(), parseContext);
            parseContext.getMetadata().create(functionName, "cType", returnType);
        }
        CCall cCall = new CCall(functionName, arguments, parseContext);
        preStatements.add(cCall);
        return cCall.getRet().getRef();
    }

    @Override
    public Expr<?> visitPostfixExpressionBrackets(CParser.PostfixExpressionBracketsContext ctx) {
        return ctx.expression().accept(this);
    }

    @Override
    public Expr<?> visitGccPrettyFunc(CParser.GccPrettyFuncContext ctx) {
        uniqueWarningLogger.write(
                Level.INFO,
                "WARNING: gcc intrinsic encountered in place of an expression, using a literal 0"
                        + " instead.\n");
        CComplexType signedInt = CComplexType.getSignedInt(parseContext);
        LitExpr<?> zero = signedInt.getNullValue();
        parseContext.getMetadata().create(zero, "cType", signedInt);
        return zero;
    }

    @Override
    public Expr<?> visitPrimaryExpressionId(CParser.PrimaryExpressionIdContext ctx) {
        final var name = ctx.Identifier().getText();
        final var variable = getVar(name);
        if (variable == null) {
            // no variable found, we try some macros..
            final var ret = fromName(name, parseContext);
            if (ret != null) {
                return ret;
            }
            // ..then enumeration constants (modeled as plain int values)
            final Long enumValue =
                    hu.bme.mit.theta.frontend.transformation.model.types.simple.Enum
                            .getConstantValue(name);
            if (enumValue != null) {
                CComplexType signedInt = CComplexType.getSignedInt(parseContext);
                LitExpr<?> litExpr = signedInt.getValue(Long.toString(enumValue));
                parseContext.getMetadata().create(litExpr, "cType", signedInt);
                return litExpr;
            }
            throw new RuntimeException("No such variable or macro: " + name);
        } else {
            return variable.getRef();
        }
    }

    @Override
    public Expr<?> visitPrimaryExpressionConstant(CParser.PrimaryExpressionConstantContext ctx) {
        String text = ctx.getText().toLowerCase();
        boolean isCharLiteral = text.startsWith("'");
        boolean isLong = text.endsWith("l");
        if (isLong) text = text.substring(0, text.length() - 1);
        // hex literals use 'p' as exponent marker ('e' is a digit); char literals are never floats
        boolean isFloatLiteral =
                !isCharLiteral
                        && (text.startsWith("0x")
                                ? text.contains("p") || text.contains(".")
                                : text.contains(".") || text.contains("e"));
        if (isFloatLiteral) {
            boolean isFloat = text.endsWith("f");
            if (isFloat) text = text.substring(0, text.length() - 1);
            checkState(!(isFloat && isLong), "A constant shall only have F or L suffix, not both!");
            int exponent, significand;
            CComplexType type;
            if (isFloat) {
                exponent = parseContext.getArchitecture().getBitWidth("float_e");
                significand = parseContext.getArchitecture().getBitWidth("float_s");
                type = CComplexType.getFloat(parseContext);
            } else if (isLong) {
                exponent = parseContext.getArchitecture().getBitWidth("longdouble_e");
                significand = parseContext.getArchitecture().getBitWidth("longdouble_s");
                type = CComplexType.getLongDouble(parseContext);
            } else {
                exponent = parseContext.getArchitecture().getBitWidth("double_e");
                significand = parseContext.getArchitecture().getBitWidth("double_s");
                type = CComplexType.getDouble(parseContext);
            }

            BigFloat bigFloat;
            if (text.startsWith("0x")) {
                throw new UnsupportedFrontendElementException(
                        "Hexadecimal FP constants are not yet supported!");
            } else if (text.startsWith("0b")) {
                throw new UnsupportedFrontendElementException(
                        "Binary FP constants are not yet supported!");
            } else {
                bigFloat = new BigFloat(text, new BinaryMathContext(significand - 1, exponent));
            }
            FpLitExpr fpLitExpr =
                    FpUtils.bigFloatToFpLitExpr(bigFloat, FpType(exponent, significand));
            parseContext.getMetadata().create(fpLitExpr, "cType", type);
            return fpLitExpr;

        } else {

            boolean negativeIsUnaryMinus = false;

            boolean isLongLong = text.endsWith("l");
            if (isLongLong) text = text.substring(0, text.length() - 1);
            boolean isUnsigned = text.endsWith("u");
            if (isUnsigned) text = text.substring(0, text.length() - 1);

            BigInteger bigInteger;
            if (text.startsWith("0x")) {
                bigInteger = new BigInteger(text.substring(2), 16);
            } else if (text.startsWith("0b")) {
                bigInteger = new BigInteger(text.substring(2), 2);
            } else if (text.startsWith("0") && text.length() > 1) {
                bigInteger = new BigInteger(text.substring(1), 8);
            } else if (text.startsWith("'\\x")) { // char c = '\x0'
                bigInteger = new BigInteger(text.substring(3, text.length() - 1), 8);
            } else if (text.startsWith("'\\")) { // char c = '\0'
                bigInteger = new BigInteger(text.substring(2, text.length() - 1), 10);
            } else if (text.startsWith("'")
                    && text.endsWith("'")
                    && text.length() == 3) { // char c = 'X'
                bigInteger = BigInteger.valueOf((int) text.charAt(1));
            } else {
                bigInteger = new BigInteger(text, 10);
                negativeIsUnaryMinus = true; // -10 is -(10)
            }

            final var size = bigInteger.bitLength();

            CComplexType unsignedLongLong = CComplexType.getUnsignedLongLong(parseContext);
            CComplexType signedLongLong = CComplexType.getSignedLongLong(parseContext);
            CComplexType unsignedLong = CComplexType.getUnsignedLong(parseContext);
            CComplexType signedLong = CComplexType.getSignedLong(parseContext);
            CComplexType unsignedInt = CComplexType.getUnsignedInt(parseContext);
            CComplexType signedInt = CComplexType.getSignedInt(parseContext);

            CComplexType type;
            if ((isLongLong || size > unsignedLong.width()) && isUnsigned) type = unsignedLongLong;
            else if (!isUnsigned
                    && (isLongLong || (size >= signedLong.width()) && negativeIsUnaryMinus))
                type = signedLongLong;
            else if ((isLong || size > unsignedInt.width()) && isUnsigned) type = unsignedLong;
            else if (!isUnsigned && (isLong || (size >= signedInt.width()) && negativeIsUnaryMinus))
                type = signedLong;
            else if (isUnsigned) type = unsignedInt;
            else type = signedInt;

            LitExpr<?> litExpr =
                    parseContext.getArithmetic() == ArchitectureConfig.ArithmeticType.bitvector
                            ? isUnsigned
                                    ? BvUtils.bigIntegerToUnsignedBvLitExpr(
                                            bigInteger, type.width())
                                    : BvUtils.bigIntegerToSignedBvLitExpr(bigInteger, type.width())
                            : Int(bigInteger);

            parseContext.getMetadata().create(litExpr, "cType", type);
            return litExpr;
        }
    }

    @Override
    public Expr<?> visitPrimaryExpressionBraceExpression(
            CParser.PrimaryExpressionBraceExpressionContext ctx) {
        if (functionVisitor != null) {
            CStatement statement = ctx.expression().accept(functionVisitor);
            preStatements.add(statement);
            return statement.getExpression();
        } else {
            return getConstExpr(ctx);
        }
    }

    @Override
    public Expr<?> visitPrimaryExpressionCompoundStatement(
            PrimaryExpressionCompoundStatementContext ctx) {
        uniqueWarningLogger.info("Primary expression compound statement");
        return null;
    }

    @Override
    public Expr<?> visitPrimaryExpressionTypeInitializer(
            PrimaryExpressionTypeInitializerContext ctx) {
        uniqueWarningLogger.info("Primary expression type initializer");
        return null;
    }

    private Expr<?> getConstExpr(PrimaryExpressionBraceExpressionContext ctx) {
        var assignments = ctx.expression().assignmentExpression();
        var assignment = assignments.get(assignments.size() - 1);
        if (assignment instanceof AssignmentExpressionConditionalExpressionContext cond) {
            return cond.conditionalExpression().logicalOrExpression().accept(this);
        } else {
            throw new RuntimeException("Assignments not supported without a function visitor.");
        }
    }

    @Override
    public Expr<?> visitPrimaryExpressionGccExtension(
            CParser.PrimaryExpressionGccExtensionContext ctx) {
        return null;
    }

    @Override
    public Expr<?> visitPrimaryExpressionStrings(CParser.PrimaryExpressionStringsContext ctx) {
        CComplexType signedInt = CComplexType.getSignedInt(parseContext);
        Expr<?> ret = signedInt.getUnitValue();
        uniqueWarningLogger.write(Level.INFO, "WARNING: using int(1) as a string constant\n");
        parseContext.getMetadata().create(ret, "cType", signedInt);
        return ret;
    }

    class PostfixVisitor extends IncludeHandlingCBaseVisitor<Function<Expr<?>, Expr<?>>> {
        @Override
        public Function<Expr<?>, Expr<?>> visitPostfixExpressionBrackets(
                PostfixExpressionBracketsContext ctx) {
            return (primary) -> {
                CComplexType arrayType = CComplexType.getType(primary, parseContext);
                if (arrayType instanceof CArray) {
                    CComplexType elemType = ((CArray) arrayType).getEmbeddedType();
                    CComplexType ptrCtype = CComplexType.getUnsignedLong(parseContext);
                    Type ptrType = ptrCtype.getSmtType();
                    Expr<?> index = ctx.accept(ExpressionVisitor.this);
                    primary = dereference(primary, index, elemType);
                    parseContext.getMetadata().create(primary, "cType", elemType);
                    return primary;
                } else if (arrayType instanceof CPointer) {
                    CComplexType elemType = ((CPointer) arrayType).getEmbeddedType();
                    CComplexType ptrCtype = CComplexType.getUnsignedLong(parseContext);
                    Type ptrType = ptrCtype.getSmtType();
                    Expr<?> index = ctx.accept(ExpressionVisitor.this);
                    primary = dereference(primary, index, elemType);
                    parseContext.getMetadata().create(primary, "cType", elemType);
                    return primary;
                } else {
                    throw new RuntimeException("Non-array expression used as array!");
                }
            };
        }

        @Override
        public Function<Expr<?>, Expr<?>> visitPostfixExpressionBraces(
                PostfixExpressionBracesContext ctx) {
            return (expr) -> {
                // A call is dispatched over the candidate set only when it goes through a
                // function POINTER variable. A plain name is called directly -- both a function
                // defined here and a library function (malloc, __VERIFIER_nondet_int, ...), which
                // is not in `functions` because it is resolved by name much later.
                boolean isDefinedFunction =
                        expr instanceof RefExpr<?> refExpr
                                && refExpr.getDecl() instanceof VarDecl<?> varDecl
                                && functions.containsKey(varDecl);
                if (!isDefinedFunction && isCallableFunctionPointer(expr)) {
                    return indirectCall(ctx, expr);
                }
                checkState(
                        expr instanceof RefExpr<?>, "Only variable-backed functions are callable.");
                CParser.ArgumentExpressionListContext exprList = ctx.argumentExpressionList();
                List<CStatement> arguments;
                if (exprList == null) arguments = List.of();
                else {
                    List<CStatement> list = new ArrayList<>();
                    for (AssignmentExpressionContext assignmentExpressionContext :
                            exprList.assignmentExpression()) {
                        if (functionVisitor == null)
                            throw new RuntimeException(
                                    "Cannot parse function calls without a function visitor.");
                        CStatement accept = assignmentExpressionContext.accept(functionVisitor);
                        list.add(accept);
                    }
                    arguments = list;
                }
                CCall cCall =
                        new CCall(((RefExpr<?>) expr).getDecl().getName(), arguments, parseContext);
                if (cCall.getFunctionId().contains("pthread")) parseContext.setMultiThreading(true);
                preStatements.add(cCall);
                if (functionVisitor != null) functionVisitor.recordMetadata(ctx, cCall);
                return cCall.getRet().getRef();
            };
        }

        @Override
        public Function<Expr<?>, Expr<?>> visitPostfixExpressionMemberAccess(
                PostfixExpressionMemberAccessContext ctx) {
            return (primary) -> {
                final CComplexType type = CComplexType.getType(primary, parseContext);
                checkState(type instanceof CStruct, "Only structs expected here");
                final CStruct structType = (CStruct) type;
                final String accName = ctx.Identifier().getText();
                final var embeddedType = structType.getFieldsAsMap().get(accName);
                checkState(
                        embeddedType != null,
                        "Field [%s] not found, available fields are: %s"
                                .formatted(accName, ((CStruct) type).getFieldsAsMap().keySet()));
                final var idxExpr =
                        type.getValue(String.valueOf(memberOffset(structType, accName)));
                primary =
                        Exprs.Dereference(
                                cast(primary, primary.getType()),
                                cast(idxExpr, primary.getType()),
                                embeddedType.getSmtType());
                parseContext.getMetadata().create(primary, "cType", embeddedType);
                return primary;
            };
        }

        @Override
        public Function<Expr<?>, Expr<?>> visitPostfixExpressionPtrMemberAccess(
                PostfixExpressionPtrMemberAccessContext ctx) {
            return (primary) -> {
                final CComplexType type = CComplexType.getType(primary, parseContext);
                checkState(
                        type instanceof CPointer || type instanceof CArray,
                        "Only pointers expected here");
                final CComplexType structTypeErased =
                        type instanceof CPointer
                                ? ((CPointer) type).getEmbeddedType()
                                : ((CArray) type).getEmbeddedType();
                checkState(structTypeErased instanceof CStruct, "Only structs expected here");
                final CStruct structType = (CStruct) structTypeErased;
                final String accName = ctx.Identifier().getText();
                final var idxExpr =
                        structTypeErased.getValue(
                                String.valueOf(memberOffset(structType, accName)));
                final var embeddedType = structType.getFieldsAsMap().get(accName);
                checkState(
                        embeddedType != null,
                        "Field [%s] not found, available fields are: %s"
                                .formatted(
                                        accName,
                                        ((CStruct) structTypeErased).getFieldsAsMap().keySet()));
                primary =
                        Exprs.Dereference(
                                cast(primary, primary.getType()),
                                cast(idxExpr, primary.getType()),
                                embeddedType.getSmtType());
                parseContext.getMetadata().create(primary, "cType", embeddedType);
                return primary;
            };
        }

        @Override
        public Function<Expr<?>, Expr<?>> visitPostfixExpressionIncrement(
                PostfixExpressionIncrementContext ctx) {
            return (primary) -> {
                CComplexType type = CComplexType.getType(primary, parseContext);
                Expr<?> expr = primary;
                expr = AbstractExprs.Add(expr, type.getUnitValue());
                parseContext.getMetadata().create(expr, "cType", type);
                expr = type.castTo(expr);
                parseContext.getMetadata().create(expr, "cType", type);
                CExpr cexpr;
                cexpr = new CExpr(expr, parseContext);
                // no need to truncate here, as left and right side types are the same
                CAssignment cAssignment = new CAssignment(primary, cexpr, "=", parseContext);
                postStatements.add(0, cAssignment);
                if (primary instanceof RefExpr
                        && atomicVars.contains(((RefExpr<?>) primary).getDecl())) {
                    preStatements.add(
                            new CCall("__VERIFIER_atomic_begin", List.of(), parseContext));
                    postStatements.add(new CCall("__VERIFIER_atomic_end", List.of(), parseContext));
                }
                if (functionVisitor != null) functionVisitor.recordMetadata(ctx, cAssignment);
                if (functionVisitor != null) functionVisitor.recordMetadata(ctx, cexpr);
                return primary;
            };
        }

        @Override
        public Function<Expr<?>, Expr<?>> visitPostfixExpressionDecrement(
                PostfixExpressionDecrementContext ctx) {
            return (primary) -> {
                CComplexType type = CComplexType.getType(primary, parseContext);
                Expr<?> expr = primary;
                expr = AbstractExprs.Sub(expr, type.getUnitValue());
                parseContext.getMetadata().create(expr, "cType", type);
                expr = type.castTo(expr);
                parseContext.getMetadata().create(expr, "cType", type);
                CExpr cexpr;
                cexpr = new CExpr(expr, parseContext);
                // no need to truncate here, as left and right side types are the same
                CAssignment cAssignment = new CAssignment(primary, cexpr, "=", parseContext);
                postStatements.add(0, cAssignment);
                if (primary instanceof RefExpr
                        && atomicVars.contains(((RefExpr<?>) primary).getDecl())) {
                    preStatements.add(
                            new CCall("__VERIFIER_atomic_begin", List.of(), parseContext));
                    postStatements.add(new CCall("__VERIFIER_atomic_end", List.of(), parseContext));
                }
                if (functionVisitor != null) functionVisitor.recordMetadata(ctx, cAssignment);
                if (functionVisitor != null) functionVisitor.recordMetadata(ctx, cexpr);
                return expr;
            };
        }
    }
}
