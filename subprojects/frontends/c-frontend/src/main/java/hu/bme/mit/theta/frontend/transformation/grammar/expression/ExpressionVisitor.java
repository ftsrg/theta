/*
 *  Copyright 2023 Budapest University of Technology and Economics
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
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs;
import hu.bme.mit.theta.core.type.anytype.IteExpr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.bvtype.BvAndExpr;
import hu.bme.mit.theta.core.type.bvtype.BvExprs;
import hu.bme.mit.theta.core.type.bvtype.BvOrExpr;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.bvtype.BvXorExpr;
import hu.bme.mit.theta.core.type.fptype.FpLitExpr;
import hu.bme.mit.theta.core.utils.BvUtils;
import hu.bme.mit.theta.core.utils.FpUtils;
import hu.bme.mit.theta.frontend.ParseContext;
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig;
import hu.bme.mit.theta.frontend.transformation.grammar.function.FunctionVisitor;
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.TypedefVisitor;
import hu.bme.mit.theta.frontend.transformation.grammar.type.TypeVisitor;
import hu.bme.mit.theta.frontend.transformation.model.declaration.CDeclaration;
import hu.bme.mit.theta.frontend.transformation.model.statements.CAssignment;
import hu.bme.mit.theta.frontend.transformation.model.statements.CCall;
import hu.bme.mit.theta.frontend.transformation.model.statements.CCompound;
import hu.bme.mit.theta.frontend.transformation.model.statements.CExpr;
import hu.bme.mit.theta.frontend.transformation.model.statements.CStatement;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.real.CReal;
import org.kframework.mpfr.BigFloat;
import org.kframework.mpfr.BinaryMathContext;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Deque;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Ite;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.FpType;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public class ExpressionVisitor extends CBaseVisitor<Expr<?>> {
    protected final List<CStatement> preStatements = new ArrayList<>();
    protected final List<CStatement> postStatements = new ArrayList<>();
    protected final Deque<Tuple2<String, Map<String, VarDecl<?>>>> variables;
    protected final Map<VarDecl<?>, CDeclaration> functions;
    private final ParseContext parseContext;
    private final FunctionVisitor functionVisitor;
    private final TypedefVisitor typedefVisitor;
    private final TypeVisitor typeVisitor;

    public ExpressionVisitor(ParseContext parseContext, FunctionVisitor functionVisitor, Deque<Tuple2<String, Map<String, VarDecl<?>>>> variables, Map<VarDecl<?>, CDeclaration> functions, TypedefVisitor typedefVisitor, TypeVisitor typeVisitor) {
        this.parseContext = parseContext;
        this.functionVisitor = functionVisitor;
        this.variables = variables;
        this.functions = functions;
        this.typedefVisitor = typedefVisitor;
        this.typeVisitor = typeVisitor;
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
    public Expr<?> visitConditionalExpression(CParser.ConditionalExpressionContext ctx) {
        if (ctx.expression() != null) {
            CStatement ifTrue = ctx.expression().accept(functionVisitor);
            addPreStatements(ifTrue);
            if (ifTrue instanceof CAssignment) {
                preStatements.add(ifTrue);
            }
            Expr<?> expr = ctx.logicalOrExpression().accept(this);
            Expr<?> lhs = ifTrue.getExpression();
            Expr<?> rhs = ctx.conditionalExpression().accept(this);
            CComplexType smallestCommonType = CComplexType.getSmallestCommonType(List.of(CComplexType.getType(lhs, parseContext), CComplexType.getType(rhs, parseContext)), parseContext);
            IteExpr<?> ite = Ite(
                    AbstractExprs.Neq(CComplexType.getType(expr, parseContext).getNullValue(), expr),
                    smallestCommonType.castTo(lhs),
                    smallestCommonType.castTo(rhs)
            );
            parseContext.getMetadata().create(ite, "cType", smallestCommonType);
            return ite;
        } else return ctx.logicalOrExpression().accept(this);
    }

    private void addPreStatements(CStatement ifTrue) {
        if (ifTrue instanceof CCompound) {
            if (ifTrue.getPreStatements() != null) preStatements.add(ifTrue.getPreStatements());
            if (ifTrue.getPostStatements() != null) postStatements.add(ifTrue.getPostStatements());
            for (CStatement cStatement : ((CCompound) ifTrue).getcStatementList()) {
                addPreStatements(cStatement);
            }
        }
    }

    @Override
    public Expr<?> visitLogicalOrExpression(CParser.LogicalOrExpressionContext ctx) {
        if (ctx.logicalAndExpression().size() > 1) {
            List<Expr<BoolType>> collect = ctx.logicalAndExpression().stream().map(logicalAndExpressionContext -> {
                Expr<?> expr = logicalAndExpressionContext.accept(this);
                return AbstractExprs.Neq(CComplexType.getType(expr, parseContext).getNullValue(), expr);
            }).collect(Collectors.toList());
            CComplexType signedInt = CComplexType.getSignedInt(parseContext);
            IteExpr<?> ite = Ite(BoolExprs.Or(collect), signedInt.getUnitValue(), signedInt.getNullValue());
            parseContext.getMetadata().create(ite, "cType", signedInt);
            return ite;
        }
        return ctx.logicalAndExpression(0).accept(this);
    }

    @Override
    public Expr<?> visitLogicalAndExpression(CParser.LogicalAndExpressionContext ctx) {
        if (ctx.inclusiveOrExpression().size() > 1) {
            List<Expr<BoolType>> collect = ctx.inclusiveOrExpression().stream().map(inclusiveOrExpression -> {
                Expr<?> expr = inclusiveOrExpression.accept(this);
                return AbstractExprs.Neq(CComplexType.getType(expr, parseContext).getNullValue(), expr);
            }).collect(Collectors.toList());
            CComplexType signedInt = CComplexType.getSignedInt(parseContext);
            IteExpr<?> ite = Ite(BoolExprs.And(collect), signedInt.getUnitValue(), signedInt.getNullValue());
            parseContext.getMetadata().create(ite, "cType", signedInt);
            return ite;
        }
        return ctx.inclusiveOrExpression(0).accept(this);
    }

    @Override
    public Expr<?> visitInclusiveOrExpression(CParser.InclusiveOrExpressionContext ctx) {
        if (ctx.exclusiveOrExpression().size() > 1) {
            List<Expr<?>> exprs = ctx.exclusiveOrExpression().stream().map(exclusiveOrExpression -> exclusiveOrExpression.accept(this)).collect(Collectors.toList());
            List<CComplexType> types = exprs.stream().map((Expr<?> expr1) -> CComplexType.getType(expr1, parseContext)).collect(Collectors.toList());
            CComplexType smallestCommonType = CComplexType.getSmallestCommonType(types, parseContext);
            List<Expr<BvType>> collect = exprs.stream().map(expr -> {
                Expr<?> ret = smallestCommonType.castTo(expr);
                checkState(ret.getType() instanceof BvType, "Non-bitvector type found!");
                //noinspection unchecked
                return (Expr<BvType>) ret;
            }).collect(Collectors.toList());
            BvOrExpr or = BvExprs.Or(collect);
            parseContext.getMetadata().create(or, "cType", smallestCommonType);
            return or;
        }
        return ctx.exclusiveOrExpression(0).accept(this);
    }

    @Override
    public Expr<?> visitExclusiveOrExpression(CParser.ExclusiveOrExpressionContext ctx) {
        if (ctx.andExpression().size() > 1) {
            List<Expr<?>> exprs = ctx.andExpression().stream().map(andExpression -> andExpression.accept(this)).collect(Collectors.toList());
            List<CComplexType> types = exprs.stream().map((Expr<?> expr1) -> CComplexType.getType(expr1, parseContext)).collect(Collectors.toList());
            CComplexType smallestCommonType = CComplexType.getSmallestCommonType(types, parseContext);
            List<Expr<BvType>> collect = exprs.stream().map(expr -> {
                Expr<?> ret = smallestCommonType.castTo(expr);
                checkState(ret.getType() instanceof BvType, "Non-bitvector type found!");
                //noinspection unchecked
                return (Expr<BvType>) ret;
            }).collect(Collectors.toList());
            BvXorExpr xor = BvExprs.Xor(collect);
            parseContext.getMetadata().create(xor, "cType", smallestCommonType);
            return xor;
        }
        return ctx.andExpression(0).accept(this);
    }

    @Override
    public Expr<?> visitAndExpression(CParser.AndExpressionContext ctx) {
        if (ctx.equalityExpression().size() > 1) {
            List<Expr<?>> exprs = ctx.equalityExpression().stream().map(equalityExpression -> equalityExpression.accept(this)).collect(Collectors.toList());
            List<CComplexType> types = exprs.stream().map((Expr<?> expr1) -> CComplexType.getType(expr1, parseContext)).collect(Collectors.toList());
            CComplexType smallestCommonType = CComplexType.getSmallestCommonType(types, parseContext);
            List<Expr<BvType>> collect = exprs.stream().map(expr -> {
                Expr<?> ret = smallestCommonType.castTo(expr);
                checkState(ret.getType() instanceof BvType, "Non-bitvector type found!");
                //noinspection unchecked
                return (Expr<BvType>) ret;
            }).collect(Collectors.toList());
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
                if (expr == null)
                    leftOp = ctx.relationalExpression(i).accept(this);
                else
                    leftOp = expr;
                rightOp = ctx.relationalExpression(i + 1).accept(this);
                CComplexType smallestCommonType = CComplexType.getSmallestCommonType(List.of(CComplexType.getType(leftOp, parseContext), CComplexType.getType(rightOp, parseContext)), parseContext);
                Expr<?> leftExpr = smallestCommonType.castTo(leftOp);
                Expr<?> rightExpr = smallestCommonType.castTo(rightOp);
                CComplexType signedInt = CComplexType.getSignedInt(parseContext);
                if (ctx.signs.get(i).getText().equals("=="))
                    expr = Ite(AbstractExprs.Eq(leftExpr, rightExpr), signedInt.getUnitValue(), signedInt.getNullValue());
                else
                    expr = Ite(AbstractExprs.Neq(leftExpr, rightExpr), signedInt.getUnitValue(), signedInt.getNullValue());
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
                if (expr == null)
                    leftOp = ctx.shiftExpression(i).accept(this);
                else
                    leftOp = expr;
                rightOp = ctx.shiftExpression(i + 1).accept(this);
                CComplexType smallestCommonType = CComplexType.getSmallestCommonType(List.of(CComplexType.getType(leftOp, parseContext), CComplexType.getType(rightOp, parseContext)), parseContext);
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
                        throw new IllegalStateException("Unexpected value: " + ctx.signs.get(i).getText());
                }
//                MaxEnumAnalyzer.instance.consume(guard); TODO: handle circular dependency
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
            CComplexType smallestCommonType = CComplexType.getSmallestCommonType(List.of(CComplexType.getType(accept, parseContext)), parseContext);
            checkState(smallestCommonType.getSmtType() instanceof BvType);
            for (int i = 1; i < ctx.additiveExpression().size(); ++i) {
                Expr<BvType> rightOp;
                accept = ctx.additiveExpression(i).accept(this);
                checkState(accept.getType() instanceof BvType);
                //noinspection unchecked
                rightOp = (Expr<BvType>) accept;
                Expr<BvType> leftExpr = cast(smallestCommonType.castTo(expr), (BvType) smallestCommonType.getSmtType());
                Expr<BvType> rightExpr = cast(smallestCommonType.castTo(rightOp), (BvType) smallestCommonType.getSmtType());
                if (ctx.signs.get(i - 1).getText().equals(">>")) {
                    //TODO: is this sound?
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
            List<Expr<?>> exprs = ctx.multiplicativeExpression().stream().map(multiplicativeExpression -> multiplicativeExpression.accept(this)).collect(Collectors.toList());
            List<CComplexType> types = exprs.stream().map((Expr<?> expr1) -> CComplexType.getType(expr1, parseContext)).collect(Collectors.toList());
            CComplexType smallestCommonType = CComplexType.getSmallestCommonType(types, parseContext);
            List<Expr<?>> collect = new ArrayList<>();
            for (int i = 0; i < exprs.size(); i++) {
                Expr<?> expr = (i == 0 || ctx.signs.get(i - 1).getText().equals("+")) ? exprs.get(i) : AbstractExprs.Neg(exprs.get(i));
                parseContext.getMetadata().create(expr, "cType", CComplexType.getType(exprs.get(i), parseContext));
                Expr<?> castTo = smallestCommonType.castTo(expr);
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
                if (expr == null)
                    leftOp = ctx.castExpression(i).accept(this);
                else
                    leftOp = expr;
                rightOp = ctx.castExpression(i + 1).accept(this);
                CComplexType smallestCommonType = CComplexType.getSmallestCommonType(List.of(CComplexType.getType(leftOp, parseContext), CComplexType.getType(rightOp, parseContext)), parseContext);
                Expr<?> leftExpr = smallestCommonType.castTo(leftOp);
                Expr<?> rightExpr = smallestCommonType.castTo(rightOp);
                switch (ctx.signs.get(i).getText()) {
                    case "*":
                        expr = AbstractExprs.Mul(leftExpr, rightExpr);
                        break;
                    case "/":
                        expr = AbstractExprs.Div(leftExpr, rightExpr);
                        break;
                    case "%":
                        expr = AbstractExprs.Mod(leftExpr, rightExpr);
                        break;
                    default:
                        throw new IllegalStateException("Unexpected value: " + ctx.signs.get(i).getText());
                }
                parseContext.getMetadata().create(expr, "cType", smallestCommonType);
                expr = smallestCommonType.castTo(expr);
                parseContext.getMetadata().create(expr, "cType", smallestCommonType);
            }
            return expr;
        }
        return ctx.castExpression(0).accept(this);
    }

    @Override
    public Expr<?> visitCastExpressionUnaryExpression(CParser.CastExpressionUnaryExpressionContext ctx) {
        return ctx.unaryExpression().accept(this);
    }

    @Override
    public Expr<?> visitCastExpressionCast(CParser.CastExpressionCastContext ctx) {
        CComplexType actualType = ctx.typeName().specifierQualifierList().accept(typeVisitor).getActualType();
        Expr<?> expr = actualType.castTo(ctx.castExpression().accept(this));
        parseContext.getMetadata().create(expr, "cType", actualType);
        expr = actualType.castTo(expr);
        parseContext.getMetadata().create(expr, "cType", actualType);
        return expr;
    }

    @Override
    public Expr<?> visitUnaryExpressionSizeOrAlignOf(CParser.UnaryExpressionSizeOrAlignOfContext ctx) {
        if (ctx.Alignof() != null) {
            System.err.println("WARNING: alignof is not yet implemented, using a literal 0 instead.");
            CComplexType signedInt = CComplexType.getSignedInt(parseContext);
            LitExpr<?> zero = signedInt.getNullValue();
            parseContext.getMetadata().create(zero, "cType", signedInt);
            return zero;
        } else {
            Optional<CComplexType> type = typedefVisitor.getType(ctx.typeName().getText());
            if (type.isPresent()) {
                LitExpr<?> value = CComplexType.getSignedInt(parseContext).getValue("" + parseContext.getArchitecture().getBitWidth(type.get().getTypeName()) / 8);
                return value;
            } else {
                System.err.println("WARNING: sizeof got unknown type, using a literal 0 instead.");
                CComplexType signedInt = CComplexType.getSignedInt(parseContext);
                LitExpr<?> zero = signedInt.getNullValue();
                parseContext.getMetadata().create(zero, "cType", signedInt);
                return zero;
            }
        }

    }

    @Override
    public Expr<?> visitUnaryExpression(CParser.UnaryExpressionContext ctx) {
        Expr<?> ret;
        if (ctx.unaryExpressionSizeOrAlignOf() != null) {
            ret = ctx.unaryExpressionSizeOrAlignOf().accept(this);
        } else {
            ret = ctx.unaryExpressionCast() == null ? ctx.postfixExpression().accept(this) : ctx.unaryExpressionCast().accept(this);
        }
        int increment = ctx.unaryExpressionIncrement().size() - ctx.unaryExpressionDecrement().size();
        if (increment != 0) {
            Expr<?> expr = ret;
            CComplexType type = CComplexType.getType(ret, parseContext);
            for (int i = 0; i < Math.abs(increment); i++) {
                if (increment < 0)
                    expr = AbstractExprs.Sub(expr, type.getUnitValue());
                else
                    expr = AbstractExprs.Add(expr, type.getUnitValue());
            }
            expr = type.castTo(expr);
            parseContext.getMetadata().create(expr, "cType", type);
            Expr<?> wrappedExpr = type.castTo(expr);
            CExpr cexpr = new CExpr(wrappedExpr, parseContext);
            CAssignment cAssignment = new CAssignment(ret, cexpr, "=", parseContext);
            preStatements.add(cAssignment);
            functionVisitor.recordMetadata(ctx, cAssignment);
            functionVisitor.recordMetadata(ctx, cexpr);
        }
        return ret;
    }

    @Override
    public Expr<?> visitUnaryExpressionCast(CParser.UnaryExpressionCastContext ctx) {
        Expr<?> accept = ctx.castExpression().accept(this);
        CComplexType type;
        switch (ctx.unaryOperator().getText()) {
            case "-": {
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
                accept = Ite(Eq(accept, CComplexType.getType(accept, parseContext).getNullValue()), signedInt.getUnitValue(), signedInt.getNullValue());
                parseContext.getMetadata().create(accept, "cType", signedInt);
                return accept;
            case "~":
                type = CComplexType.getType(accept, parseContext);
                CComplexType smallestCommonType = CComplexType.getSmallestCommonType(List.of(type), parseContext);
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
                checkState(localAccept instanceof RefExpr<?> && ((RefExpr<?>) localAccept).getDecl() instanceof VarDecl, "Referencing non-variable expressions is not allowed!");
                return reference((RefExpr<?>) localAccept);
            case "*":
                type = CComplexType.getType(accept, parseContext);
                checkState(type instanceof CPointer, "Dereferencing non-pointer expression is not allowed!");
                return dereference(accept, (CPointer) type);
        }
        return accept;
    }

    private Expr<?> dereference(Expr<?> accept, CPointer type) {
        checkState(!(CComplexType.getType(accept, parseContext) instanceof CReal), "Float pointers are not yet supported!", parseContext);
        Dereference<?, Type> of = Dereference.of(accept, type.getEmbeddedType().getSmtType());
        parseContext.getMetadata().create(of, "cType", type.getEmbeddedType());
        return of;
    }

    private Expr<?> reference(RefExpr<?> accept) {
        checkState(!(CComplexType.getType(accept, parseContext) instanceof CReal), "Float pointers are not yet supported!", parseContext);
        Reference<Type, ?> of = Reference.of(accept, CComplexType.getUnsignedLong(parseContext).getSmtType());
        parseContext.getMetadata().create(of, "cType", new CPointer(null, CComplexType.getType(accept, parseContext), parseContext));
        parseContext.getMetadata().create(accept, "referenced", true);
        parseContext.getMetadata().create(accept, "ptrValue", of.getId());
        return of;
    }

    @Override
    public Expr<?> visitPostfixExpression(CParser.PostfixExpressionContext ctx) {
        checkState(ctx.postfixExpressionMemberAccess().size() == 0 || ctx.postfixExpressionBrackets().size() == 0, "Structs of arrays are not yet supported!");
        checkState(ctx.postfixExpressionPtrMemberAccess().size() == 0, "Struct pointers are not yet supported!");
        if (ctx.postfixExpressionBraces().size() == 1) {
            checkState(ctx.postfixExpressionBrackets().size() == 0, "Arrays and functions are not yet supported together!");
            CParser.ArgumentExpressionListContext exprList = ctx.postfixExpressionBraces(0).argumentExpressionList();
            List<CStatement> arguments = exprList == null ? List.of() : exprList.assignmentExpression().stream().map(assignmentExpressionContext -> assignmentExpressionContext.accept(functionVisitor)).collect(Collectors.toList());
            CCall cCall = new CCall(ctx.primaryExpression().getText(), arguments, parseContext);
            if (ctx.primaryExpression().getText().contains("pthread"))
                parseContext.setMultiThreading(true);
            preStatements.add(cCall);
            functionVisitor.recordMetadata(ctx, cCall);
            return cCall.getRet().getRef();
        } else {
            Expr<?> primary = ctx.primaryExpression().accept(this);
            if (primary == null) {
                return null;
            } else {
                int size = ctx.postfixExpressionBrackets().size();
                for (int i = 0; i < size; i++) {
                    CComplexType arrayType = CComplexType.getType(primary, parseContext);
                    checkState(arrayType instanceof CArray, "Non-array expression used as array!");
                    Expr<?> index = ctx.postfixExpressionBrackets().get(i).accept(this);
                    primary = ArrayReadExpr.create(primary, index);
                    parseContext.getMetadata().create(primary, "cType", ((CArray) arrayType).getEmbeddedType());
                }
                size = ctx.postfixExpressionMemberAccess().size();
                if (size > 0) {
                    StringBuilder varName = new StringBuilder(ctx.primaryExpression().getText());
                    for (int i = 0; i < size; i++) {
                        varName.append(ctx.postfixExpressionMemberAccess().get(i).getText());
                    }
                    VarDecl<?> var = getVar(varName.toString());
                    if (var == null) return null;
                    primary = var.getRef();
                }
            }
            CComplexType type = CComplexType.getType(primary, parseContext);

            // we handle ++ and -- as if they were additions and assignments
            int increment = ctx.postfixExpressionIncrement().size() - ctx.postfixExpressionDecrement().size();
            if (increment != 0) {
                checkState(!(type instanceof CArray), "Raw array access not allowed!");
                Expr<?> expr = primary;
                for (int i = 0; i < Math.abs(increment); i++) {
                    if (increment < 0)
                        expr = AbstractExprs.Sub(expr, type.getUnitValue());
                    else
                        expr = AbstractExprs.Add(expr, type.getUnitValue());
                }
                parseContext.getMetadata().create(expr, "cType", type);
                expr = type.castTo(expr);
                parseContext.getMetadata().create(expr, "cType", type);
                CExpr cexpr;
                cexpr = new CExpr(expr, parseContext);
                // no need to truncate here, as left and right side types are the same
                CAssignment cAssignment = new CAssignment(primary, cexpr, "=", parseContext);
                postStatements.add(cAssignment);
                functionVisitor.recordMetadata(ctx, cAssignment);
                functionVisitor.recordMetadata(ctx, cexpr);
            }
            return primary;
        }
    }

    @Override
    public Expr<?> visitPostfixExpressionBrackets(CParser.PostfixExpressionBracketsContext ctx) {
        return ctx.expression().accept(this);
    }

    @Override
    public Expr<?> visitPrimaryExpressionId(CParser.PrimaryExpressionIdContext ctx) {
        return getVar(ctx.Identifier().getText()).getRef();
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
                throw new UnsupportedOperationException("Hexadecimal FP constants are not yet supported!");
            } else if (text.startsWith("0b")) {
                throw new UnsupportedOperationException("Binary FP constants are not yet supported!");
            } else {
                bigFloat = new BigFloat(text, new BinaryMathContext(significand, exponent));
            }
            FpLitExpr fpLitExpr = FpUtils.bigFloatToFpLitExpr(bigFloat, FpType(exponent, significand));
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

            LitExpr<?> litExpr = parseContext.getArithmetic() == ArchitectureConfig.ArithmeticType.bitvector ?
                    isUnsigned ?
                            BvUtils.bigIntegerToUnsignedBvLitExpr(bigInteger, type.width()) :
                            BvUtils.bigIntegerToSignedBvLitExpr(bigInteger, type.width()) :
                    Int(bigInteger);

            parseContext.getMetadata().create(litExpr, "cType", type);
            return litExpr;
        }

    }

    @Override
    public Expr<?> visitPrimaryExpressionBraceExpression(CParser.PrimaryExpressionBraceExpressionContext ctx) {
        CStatement statement = ctx.expression().accept(functionVisitor);
        preStatements.add(statement);
        return statement.getExpression();
    }

    @Override
    public Expr<?> visitPrimaryExpressionGccExtension(CParser.PrimaryExpressionGccExtensionContext ctx) {
        return null;
    }

    @Override
    public Expr<?> visitPrimaryExpressionStrings(CParser.PrimaryExpressionStringsContext ctx) {
        CComplexType signedInt = CComplexType.getSignedInt(parseContext);
        Expr<?> ret = signedInt.getUnitValue();
        System.err.println("Warning: using int(1) as a string constant");
        parseContext.getMetadata().create(ret, "cType", signedInt);
        return ret;
    }
}
