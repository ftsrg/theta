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
package hu.bme.mit.theta.frontend.transformation.grammar.expression;

import hu.bme.mit.theta.c.frontend.dsl.gen.CBaseVisitor;
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
import hu.bme.mit.theta.core.type.abstracttype.DivExpr;
import hu.bme.mit.theta.core.type.abstracttype.ModExpr;
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
import hu.bme.mit.theta.frontend.transformation.grammar.function.FunctionVisitor;
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.TypedefVisitor;
import hu.bme.mit.theta.frontend.transformation.grammar.type.TypeVisitor;
import hu.bme.mit.theta.frontend.transformation.model.declaration.CDeclaration;
import hu.bme.mit.theta.frontend.transformation.model.statements.CAssignment;
import hu.bme.mit.theta.frontend.transformation.model.statements.CCall;
import hu.bme.mit.theta.frontend.transformation.model.statements.CExpr;
import hu.bme.mit.theta.frontend.transformation.model.statements.CStatement;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CStruct;
import org.kframework.mpfr.BigFloat;
import org.kframework.mpfr.BinaryMathContext;

import java.math.BigInteger;
import java.util.*;
import java.util.function.Function;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.*;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Div;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Mod;
import static hu.bme.mit.theta.core.type.anytype.Exprs.Reference;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.FpType;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

// FunctionVisitor may be null, e.g., when parsing a simple C expression.

public class ExpressionVisitor extends CBaseVisitor<Expr<?>> {
    protected final List<CStatement> preStatements = new ArrayList<>();
    protected final List<CStatement> postStatements = new ArrayList<>();
    protected final Deque<Tuple2<String, Map<String, VarDecl<?>>>> variables;
    protected final Map<VarDecl<?>, CDeclaration> functions;
    private final ParseContext parseContext;
    private final FunctionVisitor functionVisitor;
    private final TypedefVisitor typedefVisitor;
    private final TypeVisitor typeVisitor;
    private final PostfixVisitor postfixVisitor;
    private final Logger uniqueWarningLogger;

    public ExpressionVisitor(
            ParseContext parseContext,
            FunctionVisitor functionVisitor,
            Deque<Tuple2<String, Map<String, VarDecl<?>>>> variables,
            Map<VarDecl<?>, CDeclaration> functions,
            TypedefVisitor typedefVisitor,
            TypeVisitor typeVisitor,
            Logger uniqueWarningLogger) {
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
        throw new RuntimeException("No such variable: " + name);
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
            CComplexType smallestCommonType =
                    CComplexType.getSmallestCommonType(types, parseContext);
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
            CComplexType smallestCommonType =
                    CComplexType.getSmallestCommonType(types, parseContext);
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
            CComplexType smallestCommonType =
                    CComplexType.getSmallestCommonType(types, parseContext);
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
                        CComplexType.getSmallestCommonType(
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
                        CComplexType.getSmallestCommonType(
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
                    CComplexType.getSmallestCommonType(
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
            CComplexType smallestCommonType =
                    CComplexType.getSmallestCommonType(types, parseContext);
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
                        CComplexType.getSmallestCommonType(
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
        Expr<?> expr = actualType.castTo(ctx.castExpression().accept(this));
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
                                            Optional.ofNullable(
                                                    CComplexType.getType(
                                                            getVar(ctx.typeName().getText())
                                                                    .getRef(),
                                                            parseContext)));

            if (type.isPresent()) {
                LitExpr<?> value =
                        CComplexType.getSignedInt(parseContext)
                                .getValue("" + type.get().width() / 8);
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
        Expr<?> accept = ctx.castExpression().accept(this);
        CComplexType type;
        switch (ctx.unaryOperator().getText()) {
            case "-":
                {
                    Expr<?> negExpr = AbstractExprs.Neg(accept);
                    type = CComplexType.getType(accept, parseContext);
                    parseContext.getMetadata().create(negExpr, "cType", type);
                    negExpr = type.castTo(negExpr);
                    parseContext.getMetadata().create(negExpr, "cType", type);
                    return negExpr;
                }
            case "+":
                return accept; // no need to update type, it remains the same
            case "!":
                CComplexType signedInt = CComplexType.getSignedInt(parseContext);
                accept =
                        Ite(
                                Eq(
                                        accept,
                                        CComplexType.getType(accept, parseContext).getNullValue()),
                                signedInt.getUnitValue(),
                                signedInt.getNullValue());
                parseContext.getMetadata().create(accept, "cType", signedInt);
                return accept;
            case "~":
                type = CComplexType.getType(accept, parseContext);
                CComplexType smallestCommonType =
                        CComplexType.getSmallestCommonType(List.of(type), parseContext);
                checkState(accept.getType() instanceof BvType);
                accept = smallestCommonType.castTo(accept);
                //noinspection unchecked
                Expr<?> expr = BvExprs.Not((Expr<BvType>) accept);
                parseContext.getMetadata().create(expr, "cType", smallestCommonType);
                expr = smallestCommonType.castTo(expr);
                parseContext.getMetadata().create(expr, "cType", smallestCommonType);
                return expr;
            case "&":
                final Expr<?> localAccept = accept;
                checkState(
                        localAccept instanceof RefExpr<?>
                                && ((RefExpr<?>) localAccept).getDecl() instanceof VarDecl,
                        "Referencing non-variable expressions is not allowed!");
                return reference((RefExpr<?>) localAccept);
            case "*":
                type = CComplexType.getType(accept, parseContext);
                if (type instanceof CPointer) type = ((CPointer) type).getEmbeddedType();
                else if (type instanceof CArray) type = ((CArray) type).getEmbeddedType();
                return dereference(
                        accept, CComplexType.getUnsignedLong(parseContext).getNullValue(), type);
        }
        return accept;
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

    private Expr<?> reference(RefExpr<?> accept) {
        final var newType =
                new CPointer(null, CComplexType.getType(accept, parseContext), parseContext);
        Reference<Type, ?> of = Reference(accept, newType.getSmtType());
        parseContext.getMetadata().create(of, "cType", newType);
        return of;
    }

    @Override
    public Expr<?> visitPostfixExpression(CParser.PostfixExpressionContext ctx) {
        Expr<?> primary = ctx.primaryExpression().accept(this);
        if (primary == null) {
            return null;
        }
        for (PostfixExpressionAccessContext pfExpr : ctx.pfExprs) {
            primary = pfExpr.accept(postfixVisitor).apply(primary);
        }
        return primary;
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
        final var variable = getVar(ctx.Identifier().getText());
        return variable.getRef();
    }

    @Override
    public Expr<?> visitPrimaryExpressionConstant(CParser.PrimaryExpressionConstantContext ctx) {
        String text = ctx.getText().toLowerCase();
        boolean isLong = text.endsWith("l");
        if (isLong) text = text.substring(0, text.length() - 1);
        if (text.contains(".") || text.contains("e")) {
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
            }

            CComplexType type;
            if (isLongLong && isUnsigned) type = CComplexType.getUnsignedLongLong(parseContext);
            else if (isLongLong) type = CComplexType.getSignedLongLong(parseContext);
            else if (isLong && isUnsigned) type = CComplexType.getUnsignedLong(parseContext);
            else if (isLong) type = CComplexType.getSignedLong(parseContext);
            else if (isUnsigned) type = CComplexType.getUnsignedInt(parseContext);
            else type = CComplexType.getSignedInt(parseContext);

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

    class PostfixVisitor extends CBaseVisitor<Function<Expr<?>, Expr<?>>> {
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
                checkState(expr instanceof RefExpr<?>, "Only variables are callable now.");
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
                final int index =
                        structType.getFields().stream().map(Tuple2::get1).toList().indexOf(accName);
                final var idxExpr = type.getValue(String.valueOf(index));
                final var embeddedType = structType.getFieldsAsMap().get(accName);
                checkState(
                        embeddedType != null,
                        "Field [%s] not found, available fields are: %s"
                                .formatted(accName, ((CStruct) type).getFieldsAsMap().keySet()));
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
                final int index =
                        structType.getFields().stream().map(Tuple2::get1).toList().indexOf(accName);
                final var idxExpr = structTypeErased.getValue(String.valueOf(index));
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
                if (functionVisitor != null) functionVisitor.recordMetadata(ctx, cAssignment);
                if (functionVisitor != null) functionVisitor.recordMetadata(ctx, cexpr);
                return expr;
            };
        }
    }
}
