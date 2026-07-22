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
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.fptype.FpType;
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
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.utils.BvUtils;
import hu.bme.mit.theta.core.utils.ExprUtils;
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
import hu.bme.mit.theta.frontend.transformation.model.statements.CCompound;
import hu.bme.mit.theta.frontend.transformation.model.statements.CExpr;
import hu.bme.mit.theta.frontend.transformation.model.statements.CIf;
import hu.bme.mit.theta.frontend.transformation.model.statements.CStatement;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CVoid;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.ByteUnionSlice;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CStruct;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.ObjectLayout;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.CInteger;
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

    /**
     * Puts the statements an operand of `&&` / `||` needs behind the short-circuit that guards it.
     *
     * <p>An operand can only be evaluated by *running* something first -- a call is lifted out into
     * a statement of its own -- and those statements land in {@link #preStatements}, which is
     * emitted ahead of the condition. That runs them unconditionally, which C says must not happen:
     * in `p && p->f`, `n != 0 && x / n`, or `x > INT_MIN && abs(x) < k`, the right-hand operand is
     * evaluated only once the left one allows it, and each of those is undefined behaviour if it is
     * not. (Dereferences do not need this -- they stay expressions, and the memsafety encoding
     * already tracks the condition guarding them -- but calls do.)
     *
     * <p>So the statements this operand added are lifted back out and re-emitted inside an `if` on
     * the operands already evaluated: all of them holding, for `&&`; none of them, for `||`.
     *
     * <p>Only statements that actually *do* something are worth this. An operand lands in {@link
     * #preStatements} for reasons that have nothing to do with side effects -- every parenthesised
     * sub-expression does, because {@code visitPrimaryExpressionBraceExpression} lifts one -- and
     * guarding those buys nothing while costing a branch. `(a && b) || (c && d)` is the whole of
     * SV-COMP's `assume_abort_if_not`, so taking "the list grew" as the signal split every such
     * condition into two paths whose arms were *identical*, and the resulting explosion timed out a
     * mass of tasks that had solved in seconds.
     */
    private void guardShortCircuited(
            int from, List<Expr<BoolType>> alreadyEvaluated, boolean stopWhenTrue) {
        if (alreadyEvaluated.isEmpty() || preStatements.size() == from) {
            return; // the first operand always runs, and an operand with no statements needs no
            // guard
        }
        if (!mustNotRunUnconditionally(preStatements.subList(from, preStatements.size()))) {
            return; // pure statements may run whether the short-circuit is taken or not
        }
        List<CStatement> guarded =
                new ArrayList<>(preStatements.subList(from, preStatements.size()));
        preStatements.subList(from, preStatements.size()).clear();

        CCompound body = compoundOf(guarded);

        List<Expr<BoolType>> reached =
                stopWhenTrue
                        ? alreadyEvaluated.stream().map(BoolExprs::Not).collect(Collectors.toList())
                        : new ArrayList<>(alreadyEvaluated);
        CComplexType signedInt = CComplexType.getSignedInt(parseContext);
        Expr<?> guard =
                Ite(BoolExprs.And(reached), signedInt.getUnitValue(), signedInt.getNullValue());
        parseContext.getMetadata().create(guard, "cType", signedInt);
        CCompound guardCompound = compoundOf(List.of(new CExpr(guard, parseContext)));
        preStatements.add(new CIf(guardCompound, body, null, parseContext));
    }

    /**
     * Whether these statements are ones C forbids from running when the short-circuit skips their
     * operand -- i.e. whether any of them has an effect. A call does (it may not even be safe to
     * make: `x > INT_MIN && abs(x) < k`), and so does an assignment or an increment. A bare
     * expression does not: it is only here because it was parenthesised, and evaluating it either
     * way is unobservable.
     *
     * <p>Anything else is guarded, on the principle that a statement whose effect we cannot account
     * for is one we must not run early.
     */
    private boolean mustNotRunUnconditionally(List<CStatement> statements) {
        return statements.stream().anyMatch(this::mustNotRunUnconditionally);
    }

    private boolean mustNotRunUnconditionally(CStatement statement) {
        if (statement == null) {
            return false;
        }
        // Every statement carries its own lifted work in these slots, and that is where a
        // parenthesised call keeps its call -- so they decide as much as the statement itself.
        if (mustNotRunUnconditionally(statement.getPreStatements())
                || mustNotRunUnconditionally(statement.getPostStatements())) {
            return true;
        }
        if (statement instanceof CCompound) {
            return mustNotRunUnconditionally(((CCompound) statement).getcStatementList());
        }
        return !(statement instanceof CExpr); // a call, an assignment, or something unrecognised
    }

    /**
     * A compound the XCFA builder can lower: its pre- and post-statement slots have to be filled
     * in, or the builder falls back to a path that insists the compound's last statement be a
     * compound too.
     */
    private CCompound compoundOf(List<CStatement> statements) {
        CCompound compound = new CCompound(parseContext);
        statements.forEach(compound::addCStatement);
        compound.setPreStatements(new CCompound(parseContext));
        compound.setPostStatements(new CCompound(parseContext));
        return compound;
    }

    @Override
    public Expr<?> visitLogicalOrExpression(CParser.LogicalOrExpressionContext ctx) {
        if (ctx.logicalAndExpression().size() > 1) {
            List<Expr<BoolType>> collect = new ArrayList<>();
            for (CParser.LogicalAndExpressionContext operand : ctx.logicalAndExpression()) {
                // `||` stops at the first operand that holds, so anything a later one needs runs
                // only if every earlier one came out false.
                int before = preStatements.size();
                Expr<?> expr = operand.accept(this);
                guardShortCircuited(before, collect, true);
                collect.add(
                        AbstractExprs.Neq(
                                CComplexType.getType(expr, parseContext).getNullValue(), expr));
            }
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
            List<Expr<BoolType>> collect = new ArrayList<>();
            for (CParser.InclusiveOrExpressionContext operand : ctx.inclusiveOrExpression()) {
                // `&&` stops at the first operand that fails, so anything a later one needs runs
                // only if every earlier one held.
                int before = preStatements.size();
                Expr<?> expr = operand.accept(this);
                guardShortCircuited(before, collect, false);
                collect.add(
                        AbstractExprs.Neq(
                                CComplexType.getType(expr, parseContext).getNullValue(), expr));
            }
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
            final Expr<?> pointerArithmetic = pointerArithmetic(ctx, exprs, types);
            if (pointerArithmetic != null) {
                return pointerArithmetic;
            }
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

    /**
     * Pointer arithmetic {@code p + i} (equivalently {@code i + p}, or {@code p - i}), as opposed to
     * ordinary integer addition. C makes such a sum a pointer, not an integer: its value is the base
     * {@code p} advanced by {@code i} elements, and the whole benchmark memory model keys object
     * sizes on the <em>base</em> expression. The default integer path instead handed the sum to
     * {@link CComplexType#getSmallestCommonType} -- which, because {@link CPointer} inherits {@link
     * CInteger}'s rank logic with an unset rank, returned an <em>integer</em> common type and wrapped
     * the result in {@code mod 2^32}. That (a) truncated a 64-bit base to 32 bits and (b) buried the
     * {@code AddExpr} under a modulo, so {@code *(p + i)}'s fold in {@code visitUnaryExpression} (and
     * {@link #foldPointerArithmetic}) -- which only peels {@code Pos} -- no longer recognized it and
     * read {@code arrays[p + i][0]} instead of {@code arrays[p][i]}: an unallocated base, a false
     * out-of-bounds/NULL-deref on the whole {@code *(dataArray + k)} family (Juliet CWE476).
     *
     * <p>Emitting a bare pointer-typed {@code Add(base, index)} -- the index cast to the index type
     * and scaled by the pointee's cell count, with no width modulo -- keeps the sum in exactly the
     * shape those folds already expect, so {@code *(p + i)} lowers to the same {@code deref(p, i)}
     * that {@code p[i]} does. Returns null (falling back to the integer path) for anything that is
     * not one pointer/array operand added to integer terms: a pointer <em>difference</em> {@code p -
     * q} is a {@code ptrdiff_t} the {@code ReferenceElimination} decomposition handles, and a sum
     * with no pointer operand is ordinary integer arithmetic.
     */
    private Expr<?> pointerArithmetic(
            CParser.AdditiveExpressionContext ctx, List<Expr<?>> exprs, List<CComplexType> types) {
        int pointerIdx = -1;
        int pointerCount = 0;
        for (int i = 0; i < types.size(); i++) {
            if (types.get(i) instanceof CPointer || types.get(i) instanceof CArray) {
                pointerCount++;
                pointerIdx = i;
            }
        }
        // Exactly one pointer/array operand, added (not subtracted), with at least one index term.
        if (pointerCount != 1 || exprs.size() < 2) {
            return null;
        }
        final boolean pointerNegated =
                pointerIdx > 0 && ctx.signs.get(pointerIdx - 1).getText().equals("-");
        if (pointerNegated) {
            return null; // `i - p` is not valid pointer arithmetic; leave it to the integer path.
        }
        final CComplexType pointerType = types.get(pointerIdx);
        final Expr<?> base = exprs.get(pointerIdx);
        final CComplexType pointee =
                pointerType instanceof CPointer p
                        ? p.getEmbeddedType()
                        : ((CArray) pointerType).getEmbeddedType();
        // A step of `p` is one *element*. For a scalar or pointer pointee that is one storage cell,
        // so the index is used as-is -- keeping `*(p + 2)` byte-for-byte identical to the correct
        // `p[2]` lowering (and, crucially, free of the `* 1` a scale would inject: an extra `MulExpr`
        // inside the resulting dereference's offset makes the assignment path misread the *load* as
        // pointer arithmetic). An aggregate element spans `cellCount(pointee)` cells and is scaled,
        // matching the subscript path's `rowOf`; a null scale (an unsized element) means no factor.
        final boolean aggregatePointee =
                pointee instanceof CArray
                        || (pointee instanceof CStruct s && !s.isUnion());
        final Expr<?> cells = aggregatePointee ? cellCountExpr(pointee) : null;
        final CComplexType indexType = CComplexType.getUnsignedLong(parseContext);
        final List<Expr<?>> indexTerms = new ArrayList<>();
        for (int i = 0; i < exprs.size(); i++) {
            if (i == pointerIdx) {
                continue;
            }
            Expr<?> term = indexType.castTo(exprs.get(i));
            if (cells != null) {
                term = indexType.castTo(Mul(List.of(indexType.castTo(term), indexType.castTo(cells))));
            }
            if (i > 0 && ctx.signs.get(i - 1).getText().equals("-")) {
                term = AbstractExprs.Neg(term);
            }
            indexTerms.add(term);
        }
        final List<Expr<?>> addOps = new ArrayList<>();
        addOps.add(base); // pointer operand kept intact -- its CPointer/CArray cType is what the
        // `*(p + i)` and subscript folds classify as the object being indexed.
        addOps.addAll(indexTerms);
        final Expr<?> ptrArith = Add(addOps);
        parseContext.getMetadata().create(ptrArith, "cType", pointerType);
        return ptrArith;
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
                            // The division itself is buried inside the Ite that adjusts the
                            // solver's
                            // rounding to C's; only that Ite is given a type below. Type the
                            // division
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

    /**
     * `__builtin_offsetof(struct S, f)` evaluates to f's *element index* in S -- the same unit
     * every member dereference uses as its offset -- so the `container_of` idiom
     * `(struct S*)((char*)p - offsetof(struct S, f))` round-trips exactly: `&obj->f` is
     * (base, index(f)), and subtracting index(f) lands back on (base, 0), the object itself.
     * Nested (`a.b`) and indexed (`a[3]`) designators are rejected: a struct-typed field holds a
     * base id of its own in this model, so no single linear offset describes them.
     */
    @Override
    public Expr<?> visitPrimaryExpressionBuiltinOffsetof(
            CParser.PrimaryExpressionBuiltinOffsetofContext ctx) {
        CComplexType type =
                ctx.typeName().specifierQualifierList().accept(typeVisitor).getActualType();
        checkState(
                type instanceof CStruct,
                "__builtin_offsetof needs a struct or union type, got: %s",
                type);
        var designator = ctx.offsetofMemberDesignator();
        if (designator.Identifier().size() != 1 || !designator.constantExpression().isEmpty()) {
            throw new UnsupportedFrontendElementException(
                    "Nested or indexed __builtin_offsetof designators are not supported: "
                            + designator.getText());
        }
        String memberName = designator.Identifier(0).getText();
        checkState(
                ((CStruct) type).getFieldsAsMap().containsKey(memberName),
                "Field [%s] not found, available fields are: %s",
                memberName,
                ((CStruct) type).getFieldsAsMap().keySet());
        CComplexType resultType = CComplexType.getUnsignedLong(parseContext);
        Expr<?> ret =
                resultType.getValue(String.valueOf(memberOffset((CStruct) type, memberName)));
        parseContext.getMetadata().create(ret, "cType", resultType);
        return ret;
    }

    /**
     * `__builtin_types_compatible_p(t1, t2)` is a compile-time 0/1. Where both types resolve
     * (plain type names), they are compared structurally. The dominant benchmark use is the
     * kernel's `__must_be_array` assert, whose arguments are `typeof(expr)` over local variables --
     * unresolvable here -- and whose value in any program that compiles is 0 (the negative-width
     * bitfield the macro wraps it in would otherwise have been a compile error), so 0 is the
     * fallback, with a warning.
     */
    @Override
    public Expr<?> visitPrimaryExpressionBuiltinTypesCompatible(
            CParser.PrimaryExpressionBuiltinTypesCompatibleContext ctx) {
        String value = "0";
        try {
            final CComplexType left =
                    ctx.typeName(0).specifierQualifierList().accept(typeVisitor).getActualType();
            final CComplexType right =
                    ctx.typeName(1).specifierQualifierList().accept(typeVisitor).getActualType();
            if (ctx.typeName(0).abstractDeclarator() == null
                    && ctx.typeName(1).abstractDeclarator() == null) {
                value = left.getClass().equals(right.getClass()) ? "1" : "0";
            } else {
                uniqueWarningLogger.write(
                        Level.INFO,
                        "WARNING: __builtin_types_compatible_p with declarators approximated as 0: "
                                + ctx.getText()
                                + "\n");
            }
        } catch (RuntimeException e) {
            uniqueWarningLogger.write(
                    Level.INFO,
                    "WARNING: __builtin_types_compatible_p approximated as 0: "
                            + ctx.getText()
                            + "\n");
        }
        final CComplexType resultType = CComplexType.getSignedInt(parseContext);
        final Expr<?> ret = resultType.getValue(value);
        parseContext.getMetadata().create(ret, "cType", resultType);
        return ret;
    }

    /**
     * `__builtin_object_size(ptr, type)` is a compile-time size query used by _FORTIFY_SOURCE
     * wrappers. The pointee object's size is not modelled, so this returns gcc's own
     * size-unknown fallback: `(size_t)-1` for types 0/1 (no upper bound, so the wrapped
     * `__*_chk` never spuriously aborts) and `0` for types 2/3. The pointer argument is not
     * evaluated -- like sizeof it has no side effects.
     */
    @Override
    public Expr<?> visitPrimaryExpressionBuiltinObjectSize(
            CParser.PrimaryExpressionBuiltinObjectSizeContext ctx) {
        final CComplexType sizeType = CComplexType.getUnsignedLong(parseContext);
        int type = 0;
        try {
            final Expr<?> folded =
                    hu.bme.mit.theta.core.utils.ExprUtils.simplify(
                            ctx.constantExpression().accept(this));
            if (folded instanceof IntLitExpr intLit) {
                type = intLit.getValue().intValueExact();
            } else if (folded instanceof hu.bme.mit.theta.core.type.bvtype.BvLitExpr bvLit) {
                type =
                        hu.bme.mit.theta.core.utils.BvUtils.neutralBvLitExprToBigInteger(bvLit)
                                .intValueExact();
            }
        } catch (RuntimeException e) {
            type = 0;
        }
        final String value =
                (type & 2) != 0
                        ? "0"
                        : java.math.BigInteger.ONE
                                .shiftLeft(sizeType.width())
                                .subtract(java.math.BigInteger.ONE)
                                .toString();
        final Expr<?> ret = sizeType.getValue(value);
        parseContext.getMetadata().create(ret, "cType", sizeType);
        return ret;
    }

    private static final String VA_ARG = "__VERIFIER_nondet_theta_va_arg";

    /**
     * Reads the next variadic argument.
     *
     * <p>The argument list itself is not modelled -- `__builtin_va_list` is an opaque stand-in --
     * so there is nothing to read *from*. The only sound answer is that the value could be anything
     * the requested type can hold: a fresh nondeterministic value of that type, which
     * `NondetFunctionPass` turns into a havoc (and which the type-range assume then keeps inside
     * the type). Over-approximate, and honest about what we do not know.
     */
    @Override
    public Expr<?> visitPrimaryExpressionBuiltinVaArg(
            CParser.PrimaryExpressionBuiltinVaArgContext ctx) {
        ctx.unaryExpression().accept(this); // the va_list operand, for any side effects it has
        String typeName = ctx.typeName().getText();
        CComplexType type =
                typedefVisitor
                        .getType(typeName)
                        .or(() -> Optional.ofNullable(CComplexType.getType(typeName, parseContext)))
                        .orElseThrow(
                                () ->
                                        new UnsupportedFrontendElementException(
                                                "Cannot resolve the type read by __builtin_va_arg: "
                                                        + typeName));
        uniqueWarningLogger.write(
                Level.INFO,
                "WARNING: __builtin_va_arg yields a nondeterministic value; the variadic argument"
                        + " list is not modeled.\n");
        parseContext.getMetadata().create(VA_ARG, "cType", type);
        CCall cCall = new CCall(VA_ARG, List.of(), parseContext);
        preStatements.add(cCall);
        return cCall.getRet().getRef();
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
                        CComplexType.getSignedInt(parseContext).getValue("" + sizeOf(type.get()));
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
            // `sizeof *p` / `sizeof x`: the operand is an expression, with or without parentheses.
            final var operand = ctx.expression() != null ? ctx.expression() : ctx.unaryExpression();
            final var expr = operand.accept(this);
            final var type = CComplexType.getType(expr, parseContext);
            LitExpr<?> value = CComplexType.getSignedInt(parseContext).getValue("" + sizeOf(type));
            return value;
        }
    }

    /**
     * How many bytes a value of this type occupies.
     *
     * <p>A struct's {@code width()} is not its size -- it is pointer-wide, like the handle a struct
     * is passed around by -- so `sizeof(struct node)` came out **4**, whatever the struct held.
     * Memory sizes are recorded from `malloc(sizeof(struct node))`, and a struct's members are
     * addressed by their *index*, so the fifth member of a five-member struct sat at offset 4 and
     * the bound check `offset < size` read `4 < 4` and called a perfectly good access an invalid
     * dereference. A struct of four members or fewer never tripped it, which is why it survived so
     * long.
     *
     * <p>The size of a struct is the size of what is in it (a union's, the largest member's).
     * Padding is not modelled -- nothing here reasons about a struct's bit-level layout, and a size
     * that is a little small would bring the bound check back down onto real accesses.
     */
    private int sizeOf(CComplexType type) {
        if (type instanceof CStruct cStruct) {
            final List<Integer> fieldSizes =
                    cStruct.getFields().stream().map(f -> sizeOf(f.get2())).toList();
            if (fieldSizes.isEmpty()) {
                return 1;
            }
            return cStruct.isUnion()
                    ? fieldSizes.stream().max(Integer::compare).orElse(1)
                    : fieldSizes.stream().mapToInt(Integer::intValue).sum();
        }
        return Math.max(type.width() / 8, 1);
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
                // A byte-laid-out union member wider than one cell (`&u.qwords[0]`): the resulting
                // pointer would have to know it reads several byte-cells as one value, which no
                // pointer in this model can express. A single byte (`&u.bytes[i]`) is a bare
                // Dereference and never reaches here (see ByteUnionSlice#WIDTH / byteScalarRead).
                final var byteUnionWidth =
                        parseContext.getMetadata().getMetadataValue(originalOperand, ByteUnionSlice.WIDTH);
                if (byteUnionWidth.isPresent() && ((Number) byteUnionWidth.get()).intValue() > 1) {
                    throw new UnsupportedFrontendElementException(
                            "Taking the address of a multi-byte member of a byte-addressed union is"
                                    + " not supported.");
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
                // `*p` where p points at an *array* denotes that array object, whose identity is
                // the pointer value itself -- there is no cell to read (the same rule `p[0]` uses
                // for a pointer to a struct). Reading a cell here would hand back the array's
                // first element as if it were the array's base, so `(*p)[i]` addressed the wrong
                // object. Wrap in Pos so the array cType lands on a fresh node, not on p's shared
                // RefExpr.
                if (type instanceof CPointer pointerToArray
                        && pointerToArray.getEmbeddedType() instanceof CArray pointeeArray) {
                    Expr<?> arrayObject = Pos(originalOperand);
                    parseContext.getMetadata().create(arrayObject, "cType", pointeeArray);
                    return arrayObject;
                }
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

    private static boolean isLiteralZero(Expr<?> expr) {
        Expr<?> stripped = stripPos(expr);
        if (stripped instanceof IntLitExpr intLit) {
            return intLit.getValue().signum() == 0;
        }
        if (stripped instanceof BvLitExpr bvLit) {
            return BvUtils.neutralBvLitExprToBigInteger(bvLit).signum() == 0;
        }
        return false;
    }

    @SuppressWarnings("unchecked")
    /**
     * Splits pointer arithmetic out of a dereference base: {@code arrays[p + i][j]} has to become
     * {@code arrays[p][i + j]}, because object sizes are keyed on the base expression and {@code p
     * + i} names no object. The unary {@code *} did this for {@code *(p + i)}; a subscript needs it
     * too, since a row of a multi-dimensional array is reached as {@code a + i*len} and then
     * indexed.
     */
    private Expr<?> foldPointerArithmetic(Expr<?> base, Expr<?> offset) {
        if (!(stripPos(base) instanceof AddExpr<?> addExpr)) {
            return null;
        }
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
        if (pointerOps.size() != 1 || indexOps.isEmpty()) {
            return null;
        }
        // Indices reaching here have their own C types -- a row offset is pointer-wide while the
        // subscript beside it is an `int` -- so they are all brought to the index type before being
        // combined, the same one `dereference` casts its offset to.
        final CComplexType indexType = CComplexType.getUnsignedLong(parseContext);
        final List<Expr<?>> casted = new ArrayList<>();
        for (Expr<?> indexOp : indexOps) {
            casted.add(indexType.castTo(indexOp));
        }
        casted.add(indexType.castTo(offset));
        return casted.size() == 1 ? casted.get(0) : Add(casted);
    }

    /**
     * The pointer-or-array operand of a sum that {@link #foldPointerArithmetic} accepted -- the
     * object the whole expression is an offset into. Only meaningful once folding succeeded, which
     * is what guarantees exactly one such operand exists.
     */
    private Expr<?> pointerBaseOf(Expr<?> sum) {
        Expr<?> pointerBase = null;
        for (Expr<?> rawOp : ((AddExpr<?>) stripPos(sum)).getOps()) {
            Expr<?> op = stripPos(rawOp);
            CComplexType opType = CComplexType.getType(op, parseContext);
            if (opType instanceof CPointer || opType instanceof CArray) {
                pointerBase = op;
            }
        }
        return pointerBase;
    }

    /**
     * Indexing an array *of arrays* selects a row, not a cell. A multi-dimensional array is one
     * contiguous object -- `int a[3][4]` is twelve cells, not three row objects -- so `a[i]` is the
     * region starting `i * 4` elements in, and `a[i][j]` lands on `arrays[a][i*4 + j]`. Returning
     * the row as plain pointer arithmetic lets the next subscript fold into the offset (see {@link
     * #foldPointerArithmetic}), and it makes a declared `int a[3][4]` and a `(int (*)[4])` view of
     * a flat buffer address the same storage -- which is what the neural-network benchmarks cast.
     *
     * <p>The row length does <b>not</b> have to be a compile-time constant. A variable-length
     * `int a[n][m]` is just as contiguous, and `i * m + j` is as good an offset when `m` is a
     * variable as when it is a literal. Requiring a literal used to send VLAs down the fallback
     * path below, where `a[i]` became a *stored base* read out of cell `i` -- a base nothing ever
     * writes, so the solver was free to make two rows the same object. That produced six false
     * alarms in the 2026-07-20 run (`array-patterns/array13` and friends, all
     * `int array[ARR_SIZE][ARR_SIZE]`): rows aliased, a summation loop read back the wrong values,
     * and a safe program was reported unsafe.
     *
     * <p>An array of <b>structs</b> is laid out the same way, scaled by the struct's cell count:
     * `s[i].f` becomes `arrays[s][i*k + f]`. That element used to be a *stored base* of its own,
     * written by one alloca per element at the declaration -- which does not scale, so above
     * {@code MAX_ELEMENT_ALLOCATIONS} the bases were simply left unwritten and two elements could
     * be conflated, the same defect the VLA rows had. Offsets need no allocation and no cap.
     *
     * <p>Nothing here derives a *base* from another base. That distinction is the whole point: base
     * ids are handed out three apart (`AllocaFunctionPass`), so an `s + i*k` used as a base would
     * become another object's base almost immediately, whereas `arrays[s][i*k + f]` stays inside
     * the row belonging to `s` and can never reach another object's row. Indexing past the end
     * lands on cells of `s`'s own row that belong to no element, which is undefined behaviour in C
     * and so constrains nothing.
     *
     * <p>Returns null only when the element is neither an array nor a struct (an ordinary cell
     * read), or when a row has no length expression at all -- an unsized `int a[][4]` parameter or
     * a flexible member, where there is genuinely nothing to scale by.
     */
    private Expr<?> rowOf(Expr<?> base, Expr<?> index, CComplexType elemType) {
        // Only an aggregate element is a *region* to be offset into; a scalar element is an
        // ordinary cell read and is left to the caller's dereference.
        final boolean aggregate =
                elemType instanceof CArray
                        || (elemType instanceof CStruct s && !s.isUnion());
        if (!aggregate) {
            return null;
        }
        final Expr<?> elementCells = cellCountExpr(elemType);
        if (elementCells == null) {
            return null;
        }
        final CComplexType indexType = CComplexType.getUnsignedLong(parseContext);
        final Expr<?> scaled =
                Mul(List.of(indexType.castTo(index), indexType.castTo(elementCells)));
        final Expr<?> row = Add(List.of(base, scaled));
        parseContext.getMetadata().create(row, "cType", elemType);
        return row;
    }

    /**
     * How many storage cells one value of [type] occupies, as an expression, or null when that
     * cannot be determined (an array with no bound).
     *
     * <p>Cells, not elements: the two coincide for scalars but not for aggregates, and scaling by
     * the wrong one silently misplaces everything. A row of `struct S a[2][3]` with a two-cell `S`
     * is *six* cells wide, so `a[1]` starts at cell 6 -- scaling by the element count 3 would land
     * it on cell 3, in the middle of row 0.
     */
    private Expr<?> cellCountExpr(CComplexType type) {
        if (type instanceof CStruct structType) {
            // A word-sliceable union is one cell: its members all share offset 0. A byte-laid-out
            // one (AD7: unionCellWidth() == null, an array member or otherwise too wide/shaped for
            // one word) needs its real ObjectLayout size in bytes instead, since that is the
            // granularity its own members are addressed at -- see [byteLaidOutMemberAccess].
            final int cells =
                    structType.isUnion()
                            ? (structType.unionCellWidth() == null
                                    ? ObjectLayout.of(structType, parseContext.getArchitecture())
                                                    .bitSize()
                                            / 8
                                    : 1)
                            : structType.getUnitCount();
            return CComplexType.getUnsignedLong(parseContext).getValue(String.valueOf(cells));
        }
        if (type instanceof CArray arrayType) {
            final Expr<?> length = arrayLengthExpr(arrayType);
            if (length == null) {
                return null;
            }
            final Expr<?> elementCells = cellCountExpr(arrayType.getEmbeddedType());
            if (elementCells == null) {
                return null;
            }
            final CComplexType indexType = CComplexType.getUnsignedLong(parseContext);
            return Mul(List.of(indexType.castTo(length), indexType.castTo(elementCells)));
        }
        // A scalar (or a pointer) occupies exactly one cell.
        return CComplexType.getUnsignedLong(parseContext).getValue("1");
    }

    /**
     * An array type's element count as an expression -- a literal where the bound is constant, the
     * bound expression itself where it is not (a VLA). Null when the type carries no bound.
     *
     * <p>Using the bound expression directly reads the size variable at the point of the *access*,
     * whereas C fixes a VLA's size when the declaration is reached. The two differ only if the
     * program assigns to that variable while the array is alive, which is rare and was already
     * mismodelled far more coarsely (the whole array was one conflated object). Left as a known
     * limitation rather than silently claimed correct; capturing the bound into a temporary at the
     * declaration is the proper fix and belongs with AD7's derived bases.
     */
    private Expr<?> arrayLengthExpr(CArray type) {
        if (type.getArrayDimension() == null) {
            return null;
        }
        return ExprUtils.simplify(type.getArrayDimension().getExpression());
    }

    private <T extends Type> Expr<?> dereference(
            Expr<?> accept, Expr<?> offset, CComplexType type) {
        final Expr<?> folded = foldPointerArithmetic(accept, offset);
        if (folded != null) {
            accept = pointerBaseOf(accept);
            offset = folded;
        }
        // An offset is an *index*, so it is cast to the index type -- the same unsigned long the
        // zero offset above and the initializer-list dereferences use, and pointer-wide in every
        // data model. It used to be cast to the *pointer's own* type, which is a `CInteger` of that
        // same width: `castTo` then returned the index expression untouched (equal width, equal
        // signedness) and stamped the pointer type onto it. That expression is the index
        // *variable*,
        // so `a[j]` quietly recorded `j` itself as an array, and every later `j++` was read as
        // pointer arithmetic and refused. Nothing about `j` is a pointer.
        Expr<?> index = CComplexType.getUnsignedLong(parseContext).castTo(offset);
        Dereference<T, ?, Type> of = Exprs.Dereference((Expr<T>) accept, index, type.getSmtType());
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
        // The GCC `__atomic_*` builtins and their C11 `atomic_*` spellings are compiler intrinsics
        // with no declaration to resolve; recognise them here and emit an ordinary call so that
        // AtomicFunctionsPass can lower each into an atomic block. Only the return *type* is decided
        // here (so the call's return variable is typed right); the semantics live in the pass.
        Expr<?> atomic = atomicBuiltinCall(name, args);
        if (atomic != null) {
            return atomic;
        }
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
            case "__builtin_va_start", "__builtin_va_end", "__builtin_va_copy" -> {
                // The argument list is not modelled -- `__builtin_va_arg` yields a fresh
                // nondeterministic value regardless -- so setting one up, copying it and tearing it
                // down have nothing to do. They are void: no one may read the value returned here.
                if (functionVisitor == null) {
                    return null;
                }
                for (AssignmentExpressionContext arg : args) {
                    arg.accept(functionVisitor); // for any side effects the operands have
                }
                CComplexType signedInt = CComplexType.getSignedInt(parseContext);
                LitExpr<?> unused = signedInt.getNullValue();
                parseContext.getMetadata().create(unused, "cType", signedInt);
                return unused;
            }
            case "__builtin_unreachable" -> {
                // The programmer promises control never gets here; reaching it is undefined. Ending
                // the path is what the compiler's contract says and it invents no error of its own,
                // which is exactly how `abort` is already modelled (FinalLocationPass turns a call
                // to it into an edge to the final location).
                return callModeledLibraryFunction("abort", List.of(), false);
            }
            case "__builtin_bswap16", "__builtin_bswap32", "__builtin_bswap64" -> {
                return byteSwap(args, Integer.parseInt(name.substring("__builtin_bswap".length())));
            }
            case "__builtin_uadd_overflow" -> {
                return unsignedOverflowBuiltin(
                        args, true, CComplexType.getUnsignedInt(parseContext));
            }
            case "__builtin_uaddl_overflow" -> {
                return unsignedOverflowBuiltin(
                        args, true, CComplexType.getUnsignedLong(parseContext));
            }
            case "__builtin_uaddll_overflow" -> {
                return unsignedOverflowBuiltin(
                        args, true, CComplexType.getUnsignedLongLong(parseContext));
            }
            case "__builtin_umul_overflow" -> {
                return unsignedOverflowBuiltin(
                        args, false, CComplexType.getUnsignedInt(parseContext));
            }
            case "__builtin_umull_overflow" -> {
                return unsignedOverflowBuiltin(
                        args, false, CComplexType.getUnsignedLong(parseContext));
            }
            case "__builtin_umulll_overflow" -> {
                return unsignedOverflowBuiltin(
                        args, false, CComplexType.getUnsignedLongLong(parseContext));
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
    /**
     * `<base>.<member>`, flattening through C11 anonymous struct/union members: `s.a` finds `a`
     * inside `struct S { union { int a; ... }; }` by first accessing the synthetic
     * {@link CStruct#ANONYMOUS_FIELD_PREFIX} field, then `a` within it. Each step is one
     * Dereference at the member's field index.
     */
    private Expr<?> structMemberAccess(Expr<?> base, CStruct structType, String memberName) {
        if (structType.getFieldsAsMap().get(memberName) != null) {
            return directMemberAccess(base, structType, memberName);
        }
        for (Tuple2<String, CComplexType> field : structType.getFields()) {
            if (field.get1().startsWith(CStruct.ANONYMOUS_FIELD_PREFIX)
                    && field.get2() instanceof CStruct anonymous
                    && hasMemberDeep(anonymous, memberName)) {
                return structMemberAccess(
                        directMemberAccess(base, structType, field.get1()), anonymous, memberName);
            }
        }
        throw new UnsupportedFrontendElementException(
                "Field [%s] not found, available fields are: %s"
                        .formatted(memberName, structType.getFieldsAsMap().keySet()));
    }

    private Expr<?> directMemberAccess(Expr<?> base, CStruct structType, String memberName) {
        final CComplexType embeddedType = structType.getFieldsAsMap().get(memberName);

        // AD7, the intractable half: a union whose members cannot share one packed word at all
        // (unionCellWidth() == null -- an array member, or one otherwise too wide/shaped for a
        // single word) has no cell for the old slicing path to use. It still does not have to be
        // refused, though: given real byte-addressed storage, `u.dwords[i]` is just bytes
        // [i*4, i*4+4), which is plain arithmetic under both encodings.
        //
        // `unionMembersShareRepresentation` is deliberately NOT consulted for the trigger, and
        // byteLaidOutMemberAccess throws its own refusal directly rather than falling back to the
        // pre-existing "differing representations" check below: that check is only meaningful for
        // the plain-integer overlay it was written for, since every aggregate type (CArray, CStruct)
        // reports the same placeholder (ptr-width, unsigned=false) width/sort/sign regardless of its
        // actual shape, so e.g. two differently-shaped arrays spuriously compare equal by it and
        // would silently alias rather than being refused.
        if (structType.isUnion()
                && structType.unionCellWidth() == null
                && !structType.getFields().isEmpty()) {
            return byteLaidOutMemberAccess(base, structType, memberName, embeddedType);
        }

        // Reading a member of a union's packed-bitfield view: its storage is the union's own cell,
        // which `base` already is, so slice that cell rather than dereferencing into a new object.
        // Slicing the same cell the sibling integer member reads is what makes the overlay alias.
        if (structType.overlayWidth() != null
                && parseContext
                        .getMetadata()
                        .getMetadataValue(
                                base,
                                hu.bme.mit.theta.frontend.transformation.model.types.complex
                                        .compound.BitfieldSlice.PACKED_CELL)
                        .isPresent()) {
            return sliceOf(base, structType.overlaySlotOf(memberName), embeddedType);
        }

        // A union whose members are not all stored alike is one word that each member slices; the
        // cell is therefore read at the union's full width rather than at this member's.
        final boolean slicedUnionMember =
                structType.isUnion()
                        && structType.unionCellWidth() != null
                        && !unionMembersShareRepresentation(structType, embeddedType);
        final CComplexType cellType =
                slicedUnionMember
                        ? unsignedIntegerOfWidth(structType.unionCellWidth())
                        : structType.isUnion()
                                        && embeddedType instanceof CStruct packed
                                        && packed.overlayWidth() != null
                                ? unsignedIntegerOfWidth(packed.overlayWidth())
                                : embeddedType;
        final Expr<?> idxExpr =
                structType.getValue(String.valueOf(memberOffset(structType, memberName)));
        // `a[i].f` on an array of structs: the subscript handed us the element as plain pointer
        // arithmetic (`a + i*k`, see #elementOf), so the member offset folds into it and the whole
        // access lands on `arrays[a][i*k + f]` -- one object, arithmetic offsets, no base derived
        // from another. Without folding, `a + i*k` would be used as a *base*, and bases are handed
        // out three apart, so element 3 of an array would collide with the next object entirely.
        // Folds to null (leaving the plain access below) whenever the base is not such a sum.
        final Expr<?> foldedOffset = foldPointerArithmetic(base, idxExpr);
        final Expr<?> accessBase = foldedOffset == null ? base : pointerBaseOf(base);
        final Expr<?> accessOffset = foldedOffset == null ? idxExpr : foldedOffset;
        final Expr<?> access =
                Exprs.Dereference(
                        cast(accessBase, accessBase.getType()),
                        cast(accessOffset, accessBase.getType()),
                        cellType.getSmtType());
        // The cell's recorded C type must match the width it was actually read at, not the
        // member's: an assignment through it casts the right-hand side to this type before
        // splicing, so recording the narrower member type here hands a 32-bit value to a 64-bit
        // cell. `sliceOf` stamps the member's own type onto the slice, which is where it belongs.
        parseContext
                .getMetadata()
                .create(access, "cType", slicedUnionMember ? cellType : embeddedType);
        if (slicedUnionMember
                && embeddedType
                        instanceof
                        hu.bme.mit.theta.frontend.transformation.model.types.complex.real.CReal
                && embeddedType.width() == structType.unionCellWidth()) {
            // A floating-point member: the cell holds its raw IEEE-754 encoding, so its value is the
            // reinterpretation of those bits, not a slice. Only the full-width case is modelled --
            // the whole cell is the float's pattern -- which is the newlib idiom
            // `union { double value; struct { uint32_t lsw, msw; } parts; }`. The cell is stamped so
            // an assignment splices FpToIeeeBv of the value back (see FrontendXcfaBuilder).
            final FpType fpType = (FpType) embeddedType.getSmtType();
            final Expr<?> value =
                    hu.bme.mit.theta.core.type.fptype.FpExprs.FromIeeeBv(
                            cast(access, (BvType) cellType.getSmtType()), fpType);
            parseContext.getMetadata().create(value, "cType", embeddedType);
            // The whole cell is the float's pattern: an assignment read-modify-writes bits [0,
            // width) -- i.e. all of them -- with FpToIeeeBv of the value (see the IEEE_FLOAT path
            // in FrontendXcfaBuilder).
            parseContext
                    .getMetadata()
                    .create(
                            value,
                            hu.bme.mit.theta.frontend.transformation.model.types.complex.compound
                                    .BitfieldSlice.CELL,
                            access);
            parseContext
                    .getMetadata()
                    .create(
                            value,
                            hu.bme.mit.theta.frontend.transformation.model.types.complex.compound
                                    .BitfieldSlice.OFFSET,
                            0);
            parseContext
                    .getMetadata()
                    .create(
                            value,
                            hu.bme.mit.theta.frontend.transformation.model.types.complex.compound
                                    .BitfieldSlice.WIDTH,
                            structType.unionCellWidth());
            parseContext
                    .getMetadata()
                    .create(
                            value,
                            hu.bme.mit.theta.frontend.transformation.model.types.complex.compound
                                    .BitfieldSlice.IEEE_FLOAT,
                            true);
            return value;
        }
        if (slicedUnionMember
                && embeddedType instanceof CStruct packed
                && packed.overlayWidth() != null) {
            // A packed-struct member of the union (`union { double value; struct {...} parts; }`).
            // When it occupies the whole cell -- overlay width == cell width, the usual case -- the
            // cell *is* the member, so return the Dereference itself with the PACKED_CELL mark. That
            // matters for a nested write like `u.parts.msw = x`: the read-modify-write needs a real
            // cell to slice, and a sliceOf wrapper (an Ite/arithmetic expression) is not one. A
            // narrower packed member is genuinely a slice.
            final var slot = structType.unionSlotOf(memberName);
            final Expr<?> cellExpr =
                    slot.bitOffset() == 0 && slot.width() == structType.unionCellWidth()
                            ? access
                            : sliceOf(
                                    access, slot, unsignedIntegerOfWidth(packed.overlayWidth()));
            parseContext.getMetadata().create(cellExpr, "cType", embeddedType);
            parseContext
                    .getMetadata()
                    .create(
                            cellExpr,
                            hu.bme.mit.theta.frontend.transformation.model.types.complex.compound
                                    .BitfieldSlice.PACKED_CELL,
                            true);
            return cellExpr;
        }
        if (slicedUnionMember) {
            // A plain-integer member: its value is a slice of the union's word. `sliceOf` carries
            // the cell along as metadata, so assigning to it read-modify-writes just its bits and
            // leaves the rest of the word -- whatever the sibling members hold -- intact.
            return sliceOf(access, structType.unionSlotOf(memberName), embeddedType);
        }
        if (cellType != embeddedType) {
            // The union's cell, read at the packed view's integer width: mark it so member
            // accesses on it slice instead of dereferencing.
            parseContext
                    .getMetadata()
                    .create(
                            access,
                            hu.bme.mit.theta.frontend.transformation.model.types.complex.compound
                                    .BitfieldSlice.PACKED_CELL,
                            true);
            return access;
        }

        // A bitfield narrower than its base type shares its cell with the rest of its run, so its
        // *value* is a slice of that cell rather than the whole of it.
        final hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.BitfieldLayout
                        .Slot
                slot = structType.isUnion() ? null : structType.slotOf(memberName);
        if (slot != null && slot.bitfield() && slot.width() < embeddedType.width()) {
            return bitfieldSliceOf(access, structType, memberName, embeddedType);
        }
        return access;
    }

    /**
     * Reads [memberName] of a byte-laid-out union (AD7): a plain scalar/pointer member reads
     * straight from its own byte cells via {@link ByteUnionSlice}; an array member returns a marker
     * for the next {@code [i]} to resolve, since {@code u.dwords[i]} is bytes {@code [i*4, i*4+4)} --
     * an arithmetic offset the subscript computes, not something a bare member access can resolve by
     * itself. Throws for a shape not (yet) supported here -- a bitfield, a floating-point member, a
     * nested aggregate, or an array of either -- rather than returning null and falling back to the
     * pre-existing "differing representations" check, which is unsound for this purpose (see below).
     */
    private Expr<?> byteLaidOutMemberAccess(
            Expr<?> base, CStruct structType, String memberName, CComplexType embeddedType) {
        // This union cannot be one packed word (the caller already checked unionCellWidth() ==
        // null), so every member access below either resolves to real byte cells or is refused
        // outright -- deliberately NOT by falling back to the pre-existing "differing
        // representations" check, which compares an aggregate's *placeholder* representation
        // (every CStruct/CArray reports the same generic ptr-width/unsigned=false triple regardless
        // of its actual shape) and so would let two differently-shaped aggregates alias silently
        // instead of refusing them.
        if (isBitfieldMember(structType, memberName)) {
            throw unsupportedByteLaidOutMember(
                    memberName, "a bitfield is not a whole number of bytes");
        }
        final ArchitectureConfig.ArchitectureType arch = parseContext.getArchitecture();
        final ObjectLayout.Field field = ObjectLayout.of(structType, arch).field(memberName);
        if (field == null) {
            throw unsupportedByteLaidOutMember(memberName, "its layout could not be determined");
        }
        final Expr<?> byteOffset = indexLiteral(field.bitOffset() / 8);
        if (embeddedType instanceof CArray arrayType) {
            final CComplexType elemType = arrayType.getEmbeddedType();
            if (elemType instanceof
                    hu.bme.mit.theta.frontend.transformation.model.types.complex.real.CReal) {
                throw unsupportedByteLaidOutMember(
                        memberName, "a floating-point element is not supported");
            }
            if (!isByteAddressableScalar(elemType)) {
                throw unsupportedByteLaidOutMember(
                        memberName, "a nested aggregate element is not supported");
            }
            final int elemBytes = ObjectLayout.sizeBits(elemType, arch) / 8;
            if (elemBytes <= 0) {
                throw unsupportedByteLaidOutMember(memberName, "its element has no static size");
            }
            // A marker for the next `[i]`: wrapped in Pos so the metadata lands on a fresh node, not
            // on `base`'s own (which already carries the union's cType and must keep it).
            final Expr<?> marker = Pos(base);
            parseContext.getMetadata().create(marker, "cType", embeddedType);
            parseContext.getMetadata().create(marker, ByteUnionSlice.ARRAY_BASE, base);
            parseContext.getMetadata().create(marker, ByteUnionSlice.ARRAY_OFFSET, byteOffset);
            parseContext.getMetadata().create(marker, ByteUnionSlice.ARRAY_ELEMENT_BYTES, elemBytes);
            return marker;
        }
        if (embeddedType instanceof
                hu.bme.mit.theta.frontend.transformation.model.types.complex.real.CReal) {
            // The batch-59 NaN gate on fpToIEEEBV stands here too, not just on the word-sliceable
            // path: a floating-point member is refused rather than reopening the unsound round-trip.
            throw unsupportedByteLaidOutMember(
                    memberName, "a floating-point member is not supported");
        }
        if (!isByteAddressableScalar(embeddedType)) {
            throw unsupportedByteLaidOutMember(memberName, "a nested aggregate is not supported");
        }
        final int widthBytes = ObjectLayout.sizeBits(embeddedType, arch) / 8;
        if (widthBytes <= 0) {
            throw unsupportedByteLaidOutMember(memberName, "it has no static size");
        }
        return byteScalarRead(base, byteOffset, widthBytes, embeddedType);
    }

    private static UnsupportedFrontendElementException unsupportedByteLaidOutMember(
            String memberName, String reason) {
        return new UnsupportedFrontendElementException(
                "Accessing member [%s] of a byte-addressed union is not supported: %s."
                        .formatted(memberName, reason));
    }

    /** Whether [memberName] of [structType] was declared as a bitfield (a non-whole-byte width). */
    private boolean isBitfieldMember(CStruct structType, String memberName) {
        final List<Tuple2<String, CComplexType>> fields = structType.getFields();
        for (int i = 0; i < fields.size(); i++) {
            if (fields.get(i).get1().equals(memberName)) {
                return structType.declaredBitfieldWidth(i) >= 0;
            }
        }
        return false;
    }

    /**
     * Whether [type] can sit in a byte-laid-out union's cells directly: a plain integer or a
     * pointer, both of which are always a whole number of bytes wide. Excludes a nested
     * struct/union (needs its own base id, not a flat byte run) and a floating-point type (the
     * batch-59 NaN gate on `fpToIEEEBV`, deliberately not reopened here).
     */
    private boolean isByteAddressableScalar(CComplexType type) {
        return isPlainInteger(type) || type instanceof CPointer;
    }

    /** A literal of the current arithmetic's index type ({@code unsigned long}), for a byte offset. */
    private Expr<?> indexLiteral(long value) {
        return CComplexType.getUnsignedLong(parseContext).getValue(String.valueOf(value));
    }

    /**
     * The value of an {@code widthBytes}-byte little-endian member starting at byte [byteOffset] of
     * the byte-laid-out union [base] is stored in. A single unsigned byte is returned bare -- the
     * Dereference itself -- so that {@code &u.bytes[i]} stays a directly addressable pointer rather
     * than being wrapped into a non-lvalue expression; anything wider (or signed) is the {@link
     * ByteUnionSlice#read} recombination of its cells, which the write side of an assignment through
     * it later splits back into cells (see {@code FrontendXcfaBuilder}).
     */
    private Expr<?> byteScalarRead(
            Expr<?> base, Expr<?> byteOffset, int widthBytes, CComplexType memberType) {
        final boolean signed = !effectivelyUnsigned(memberType);
        final CComplexType byteType = unsignedIntegerOfWidth(8);
        if (widthBytes == 1 && !signed) {
            final Expr<?> cell = byteCellAt(base, byteOffset, 0, byteType);
            parseContext.getMetadata().create(cell, "cType", memberType);
            stampByteUnionMetadata(cell, base, byteOffset, 1);
            return cell;
        }
        final List<Expr<?>> cells = new ArrayList<>(widthBytes);
        for (int j = 0; j < widthBytes; j++) {
            cells.add(byteCellAt(base, byteOffset, j, byteType));
        }
        final Expr<?> combined = ByteUnionSlice.read(cells, signed);
        final Expr<?> value = memberType.castTo(combined);
        parseContext.getMetadata().create(value, "cType", memberType);
        stampByteUnionMetadata(value, base, byteOffset, widthBytes);
        return value;
    }

    /** The one-byte cell at [byteOffset]{@code + j} of the byte-laid-out union [base]. */
    private Expr<?> byteCellAt(Expr<?> base, Expr<?> byteOffset, int j, CComplexType byteType) {
        final CComplexType indexType = CComplexType.getUnsignedLong(parseContext);
        final Expr<?> off =
                j == 0
                        ? byteOffset
                        : Add(indexType.castTo(byteOffset), indexType.castTo(indexLiteral(j)));
        final Expr<?> deref =
                Exprs.Dereference(
                        cast(base, base.getType()), cast(off, base.getType()), byteType.getSmtType());
        parseContext.getMetadata().create(deref, "cType", byteType);
        return deref;
    }

    /** Stamps the metadata an assignment through [value] needs to write its cells back individually. */
    private void stampByteUnionMetadata(
            Expr<?> value, Expr<?> base, Expr<?> byteOffset, int widthBytes) {
        parseContext.getMetadata().create(value, ByteUnionSlice.BASE, base);
        parseContext.getMetadata().create(value, ByteUnionSlice.OFFSET, byteOffset);
        parseContext.getMetadata().create(value, ByteUnionSlice.WIDTH, widthBytes);
    }

    /**
     * `u.dwords[i]` on a byte-laid-out union's array member: the marker [directMemberAccess] left on
     * `u.dwords` carries the array's own base and starting byte offset, so the subscript resolves to
     * bytes {@code [byteOff + i*elemBytes, byteOff + i*elemBytes + elemBytes)} -- plain arithmetic
     * even for a variable (nondeterministic) [indexExpr], which is the whole point of byte
     * addressing over a variable bit-shift.
     */
    private Expr<?> byteLaidOutArraySubscript(Expr<?> marker, Expr<?> indexExpr) {
        final CComplexType arrayCType = CComplexType.getType(marker, parseContext);
        final CComplexType elemType = ((CArray) arrayCType).getEmbeddedType();
        final Expr<?> base =
                (Expr<?>)
                        parseContext
                                .getMetadata()
                                .getMetadataValue(marker, ByteUnionSlice.ARRAY_BASE)
                                .orElseThrow();
        final Expr<?> startOffset =
                (Expr<?>)
                        parseContext
                                .getMetadata()
                                .getMetadataValue(marker, ByteUnionSlice.ARRAY_OFFSET)
                                .orElseThrow();
        final int elemBytes =
                (Integer)
                        parseContext
                                .getMetadata()
                                .getMetadataValue(marker, ByteUnionSlice.ARRAY_ELEMENT_BYTES)
                                .orElseThrow();
        final CComplexType indexType = CComplexType.getUnsignedLong(parseContext);
        final Expr<?> byteOffset =
                Add(
                        indexType.castTo(startOffset),
                        Mul(
                                indexType.castTo(indexExpr),
                                indexType.castTo(indexLiteral(elemBytes))));
        return byteScalarRead(base, byteOffset, elemBytes, elemType);
    }

    /**
     * The value of bitfield [memberName] read out of [cell], with the cell carried along as
     * metadata so an assignment to this member read-modify-writes just its bits instead of
     * clobbering the neighbours sharing the cell.
     */
    /** The unsigned integer type holding [bits], for reading a union's cell as one packed word. */
    private CComplexType unsignedIntegerOfWidth(int bits) {
        return switch (bits) {
            case 8 ->
                    new hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cchar
                            .CUnsignedChar(null, parseContext);
            case 16 ->
                    new hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cshort
                            .CUnsignedShort(null, parseContext);
            case 32 -> CComplexType.getUnsignedInt(parseContext);
            default -> CComplexType.getUnsignedLong(parseContext);
        };
    }

    private Expr<?> bitfieldSliceOf(
            Expr<?> cell, CStruct structType, String memberName, CComplexType memberType) {
        return sliceOf(cell, structType.slotOf(memberName), memberType);
    }

    private Expr<?> sliceOf(
            Expr<?> cell,
            hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.BitfieldLayout
                            .Slot
                    slot,
            CComplexType memberType) {
        final boolean signed =
                memberType
                                instanceof
                                hu.bme.mit.theta.frontend.transformation.model.types.complex.integer
                                                .CInteger
                                        integer
                        && integer.isSsigned();
        // The slice comes back in the *cell's* width; a member narrower than the cell it shares --
        // `lo` in a 64-bit word, say -- has to be brought down to its own type, or every later use
        // of it compares a 64-bit value against a 32-bit one.
        final Expr<?> value =
                memberType.castTo(
                        hu.bme.mit.theta.frontend.transformation.model.types.complex.compound
                                .BitfieldSlice.read(
                                cell, slot.bitOffset(), slot.width(), signed));
        parseContext.getMetadata().create(value, "cType", memberType);
        parseContext
                .getMetadata()
                .create(
                        value,
                        hu.bme.mit.theta.frontend.transformation.model.types.complex.compound
                                .BitfieldSlice.CELL,
                        cell);
        parseContext
                .getMetadata()
                .create(
                        value,
                        hu.bme.mit.theta.frontend.transformation.model.types.complex.compound
                                .BitfieldSlice.OFFSET,
                        slot.bitOffset());
        parseContext
                .getMetadata()
                .create(
                        value,
                        hu.bme.mit.theta.frontend.transformation.model.types.complex.compound
                                .BitfieldSlice.WIDTH,
                        slot.width());
        return value;
    }

    private static boolean hasMemberDeep(CStruct structType, String memberName) {
        if (structType.getFieldsAsMap().containsKey(memberName)) {
            return true;
        }
        for (Tuple2<String, CComplexType> field : structType.getFields()) {
            if (field.get1().startsWith(CStruct.ANONYMOUS_FIELD_PREFIX)
                    && field.get2() instanceof CStruct anonymous
                    && hasMemberDeep(anonymous, memberName)) {
                return true;
            }
        }
        return false;
    }

    private int memberOffset(CStruct compound, String memberName) {
        if (!compound.isUnion()) {
            // The member's storage cell: its own for an ordinary member, the shared unit for a
            // packed bitfield. Bitfield-free structs give unitOffsetOf == field position, so this
            // is byte-for-byte the historical index.
            return compound.unitOffsetOf(memberName);
        }
        CComplexType accessed = compound.getFieldsAsMap().get(memberName);
        if (accessed != null && !unionMembersShareRepresentation(compound, accessed)) {
            // Members of different widths still share the union's one cell -- a narrower one is the
            // low bits of it -- so the access can slice instead of being refused. Only shapes a
            // single word cannot hold (an array member, a float needing bit reinterpretation) still
            // reach the rejection below.
            if (compound.unionCellWidth() != null) {
                return 0;
            }
        }
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
     * <p>Not the C class, but the storage the model gives the value: same SMT sort, same width,
     * same signedness. Requiring identical classes was too strict -- the pervasive
     * {@code union { void *ptr; size_t i; }} idiom pairs a pointer with a pointer-wide unsigned
     * integer, which occupy their shared cell identically, yet their classes differ. Width must be
     * checked explicitly because under integer arithmetic every integer type is the same unbounded
     * {@code Int}, so an {@code int} and a {@code char} share an SMT sort though {@code u.i = 300;
     * u.c} must be 44, not 300; signedness likewise, so {@code int}/{@code unsigned} do not alias
     * where the sign reinterpretation would be lost.
     */
    /** Whether every member of [compound] occupies its cell exactly as [accessed] does. */
    private boolean unionMembersShareRepresentation(CStruct compound, CComplexType accessed) {
        for (Tuple2<String, CComplexType> field : compound.getFields()) {
            if (!sameRepresentation(accessed, field.get2())) {
                return false;
            }
        }
        return true;
    }

    private static boolean sameRepresentation(CComplexType a, CComplexType b) {
        // A struct of integers laid end to end is stored as the single word those bits make up, so
        // it shares a union's cell with a sibling integer of that width -- both the all-bitfield
        // overlay and `struct { uint32_t lo; uint32_t hi; }` over a `uint64_t raw`.
        final Integer leftOverlay = a instanceof CStruct left ? left.overlayWidth() : null;
        final Integer rightOverlay = b instanceof CStruct right ? right.overlayWidth() : null;
        if (leftOverlay != null || rightOverlay != null) {
            final int leftWidth = leftOverlay != null ? leftOverlay : a.width();
            final int rightWidth = rightOverlay != null ? rightOverlay : b.width();
            // A packed word is just bits; the side that is a real value still has to be a plain
            // integer of the same width for the two to name the same storage.
            final boolean leftOk = leftOverlay != null || isPlainInteger(a);
            final boolean rightOk = rightOverlay != null || isPlainInteger(b);
            return leftWidth == rightWidth && leftOk && rightOk;
        }
        return a.getSmtType().equals(b.getSmtType())
                && a.width() == b.width()
                && effectivelyUnsigned(a) == effectivelyUnsigned(b);
    }

    private static boolean isPlainInteger(CComplexType type) {
        return type
                        instanceof
                        hu.bme.mit.theta.frontend.transformation.model.types.complex.integer
                                        .CInteger
                && !(type instanceof CStruct)
                && !(type instanceof CArray)
                && !(type instanceof CPointer);
    }

    /** A pointer is an unsigned address; an integer's signedness is its own; else unsigned=false. */
    private static boolean effectivelyUnsigned(CComplexType t) {
        if (t instanceof hu.bme.mit.theta.frontend.transformation.model.types.complex.compound
                        .CPointer) {
            return true;
        }
        if (t
                instanceof
                hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.CInteger ci) {
            return !ci.isSsigned();
        }
        return false;
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
     *
     * <p>The width the overflow is computed at is fixed by the builtin's name -- {@code
     * uadd}/{@code umul} are {@code unsigned int}, {@code uaddl}/{@code umull} are {@code unsigned
     * long}, the {@code ll} forms are {@code unsigned long long} -- and is <em>not</em> read from
     * {@code res}. A caller may legitimately pass a wider {@code res} (aws-c-common writes a 32-bit
     * {@code __builtin_uadd_overflow} through an {@code unsigned long}); taking the width from
     * {@code res} then computes the addition in 64 bits, where two 32-bit operands can never
     * overflow, and the call wrongly reports "no overflow" -- a false {@code unreach-call} across
     * the whole aws saturating-arithmetic suite. The wrapped result is truncated to the builtin's
     * width, then cast to {@code res}'s type for the store.
     */
    private Expr<?> unsignedOverflowBuiltin(
            List<AssignmentExpressionContext> args, boolean isAddition, CComplexType type) {
        if (functionVisitor == null || args.size() != 3) {
            return null;
        }
        Expr<?> a = args.get(0).accept(functionVisitor).getExpression();
        Expr<?> b = args.get(1).accept(functionVisitor).getExpression();
        Expr<?> resultPointer = args.get(2).accept(functionVisitor).getExpression();
        if (!(CComplexType.getType(resultPointer, parseContext) instanceof CPointer pointer)) {
            return null;
        }
        CComplexType storeType = pointer.getEmbeddedType();

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

        Expr<?> stored = typed(storeType.castTo(wrapped), storeType);
        Expr<?> target =
                dereference(
                        resultPointer,
                        CComplexType.getUnsignedLong(parseContext).getNullValue(),
                        storeType);
        preStatements.add(
                new CAssignment(target, new CExpr(stored, parseContext), "=", parseContext));
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
    /** The type a pointer (or array) points at, or null if the expression is neither. */
    private CComplexType pointeeOf(Expr<?> pointer) {
        CComplexType type = CComplexType.getType(pointer, parseContext);
        if (type instanceof CPointer cPointer) {
            return cPointer.getEmbeddedType();
        }
        if (type instanceof CArray cArray) {
            return cArray.getEmbeddedType();
        }
        return null;
    }

    // The GCC/C11 atomic builtins, grouped by what their call *returns* -- the only thing that has
    // to be decided in the frontend so the return variable is typed correctly. The operations
    // themselves (load/store/RMW/CAS/fence, each wrapped in an atomic block) are lowered by
    // AtomicFunctionsPass, which owns the authoritative name lists; keep these in sync with it.
    private static final java.util.Set<String> ATOMIC_RETURNS_POINTEE =
            java.util.Set.of(
                    "__atomic_load_n",
                    "__atomic_load",
                    "atomic_load",
                    "atomic_load_explicit",
                    "__atomic_exchange_n",
                    "atomic_exchange",
                    "atomic_exchange_explicit",
                    "__atomic_fetch_add",
                    "__atomic_fetch_sub",
                    "__atomic_fetch_or",
                    "__atomic_fetch_and",
                    "__atomic_fetch_xor",
                    "__atomic_fetch_nand",
                    "atomic_fetch_add",
                    "atomic_fetch_sub",
                    "atomic_fetch_or",
                    "atomic_fetch_and",
                    "atomic_fetch_xor",
                    "atomic_fetch_add_explicit",
                    "atomic_fetch_sub_explicit",
                    "atomic_fetch_or_explicit",
                    "atomic_fetch_and_explicit",
                    "atomic_fetch_xor_explicit",
                    "__atomic_add_fetch",
                    "__atomic_sub_fetch",
                    "__atomic_or_fetch",
                    "__atomic_and_fetch",
                    "__atomic_xor_fetch",
                    "__atomic_nand_fetch");
    private static final java.util.Set<String> ATOMIC_RETURNS_VOID =
            java.util.Set.of(
                    "__atomic_store_n",
                    "__atomic_store",
                    "atomic_store",
                    "atomic_store_explicit",
                    "atomic_init",
                    "__atomic_exchange", // ret is by pointer, the call value is unused
                    "__atomic_thread_fence",
                    "__atomic_signal_fence",
                    "atomic_thread_fence",
                    "atomic_signal_fence");
    private static final java.util.Set<String> ATOMIC_RETURNS_INT =
            java.util.Set.of(
                    "__atomic_compare_exchange_n",
                    "__atomic_compare_exchange",
                    "atomic_compare_exchange_strong",
                    "atomic_compare_exchange_weak",
                    "atomic_compare_exchange_strong_explicit",
                    "atomic_compare_exchange_weak_explicit");

    /**
     * If [name] is an atomic builtin, emit it as a call (so {@code AtomicFunctionsPass} can lower it)
     * with its return variable typed correctly, and return the call's value. Returns null otherwise,
     * so ordinary builtin handling proceeds.
     */
    private Expr<?> atomicBuiltinCall(String name, List<AssignmentExpressionContext> args) {
        if (ATOMIC_RETURNS_POINTEE.contains(name)) {
            return atomicCall(name, args, AtomicReturn.POINTEE);
        }
        if (ATOMIC_RETURNS_VOID.contains(name)) {
            return atomicCall(name, args, AtomicReturn.VOID);
        }
        if (ATOMIC_RETURNS_INT.contains(name)) {
            return atomicCall(name, args, AtomicReturn.INT);
        }
        return null;
    }

    private enum AtomicReturn {
        POINTEE,
        INT,
        VOID,
    }

    private Expr<?> atomicCall(
            String name, List<AssignmentExpressionContext> args, AtomicReturn returnKind) {
        if (functionVisitor == null) {
            return null;
        }
        List<CStatement> arguments = new ArrayList<>();
        for (AssignmentExpressionContext arg : args) {
            arguments.add(arg.accept(functionVisitor));
        }
        CComplexType returnType;
        if (returnKind == AtomicReturn.POINTEE && !arguments.isEmpty()) {
            // load/exchange/fetch return the value at the object -- the pointee of the first argument.
            CComplexType pointee = pointeeOf(arguments.get(0).getExpression());
            returnType = pointee != null ? pointee : CComplexType.getSignedInt(parseContext);
        } else {
            // compare-exchange returns a bool (int); store and fence are void (value unused).
            returnType = CComplexType.getSignedInt(parseContext);
        }
        parseContext.getMetadata().create(name, "cType", returnType);
        CCall cCall = new CCall(name, arguments, parseContext);
        preStatements.add(cCall);
        return cCall.getRet().getRef();
    }

    /**
     * `__builtin_bswapN(x)` reverses the order of x's bytes -- so it is exactly x's bytes, taken
     * apart and put back together the other way round. Stated on the bits directly rather than with
     * the usual tower of shifts and masks: there is nothing to get wrong in a concatenation.
     *
     * <p>Bitvectors only, which is why `BitwiseChecker` marks a program that calls this as needing
     * them: reversing bytes is meaningless for a mathematical integer.
     */
    private Expr<?> byteSwap(List<AssignmentExpressionContext> args, int width) {
        if (args.isEmpty()) {
            return null;
        }
        Expr<?> value = args.get(0).accept(this);
        CComplexType type = CComplexType.getType(value, parseContext);
        if (!(type instanceof CInteger) || type.width() != width) {
            return null; // not the width the builtin names: leave it to fail loudly
        }
        Expr<BvType> bits = cast(value, BvType.of(width));
        List<Expr<BvType>> bytes = new ArrayList<>();
        // Concat puts its first operand in the *high* bits, so walking the bytes upwards from bit 0
        // and concatenating in that order is precisely the reversal.
        for (int low = 0; low < width; low += 8) {
            bytes.add(BvExprs.Extract(bits, Int(low), Int(low + 8)));
        }
        Expr<?> swapped = BvExprs.Concat(bytes);
        parseContext.getMetadata().create(swapped, "cType", type);
        return swapped;
    }

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
        return statementExpression(ctx.compoundStatement());
    }

    /**
     * A GNU statement expression `({ stmt; ...; last; })`: the statements run for their effects
     * (they are queued like any other side effect of the surrounding expression) and the last
     * statement's value is the expression's value. This is what `container_of` expands to. When
     * there is no value to yield -- no function visitor, or the block does not end in an
     * expression -- fall back to the old null result: in statement position the value is
     * discarded anyway, and a value position fails downstream exactly as it always did.
     */
    private Expr<?> statementExpression(CParser.CompoundStatementContext ctx) {
        if (functionVisitor == null) {
            return null;
        }
        CStatement statement = ctx.accept(functionVisitor);
        Expr<?> value;
        try {
            value = statement.getExpression();
        } catch (RuntimeException e) {
            value = null;
        }
        if (value == null) {
            uniqueWarningLogger.write(
                    Level.INFO, "WARNING: statement expression yields no value\n");
            return null;
        }
        preStatements.add(statement);
        return value;
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
        return statementExpression(ctx.compoundStatement());
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
                // A byte-laid-out union's array member, not yet subscripted (see
                // ByteUnionSlice#ARRAY_BASE): resolve straight to its byte cells instead of the
                // generic array/pointer path below, which knows nothing about byte granularity.
                if (parseContext
                        .getMetadata()
                        .getMetadataValue(primary, ByteUnionSlice.ARRAY_BASE)
                        .isPresent()) {
                    Expr<?> index = ctx.accept(ExpressionVisitor.this);
                    return byteLaidOutArraySubscript(primary, index);
                }
                CComplexType arrayType = CComplexType.getType(primary, parseContext);
                if (arrayType instanceof CArray) {
                    CComplexType elemType = ((CArray) arrayType).getEmbeddedType();
                    CComplexType ptrCtype = CComplexType.getUnsignedLong(parseContext);
                    Type ptrType = ptrCtype.getSmtType();
                    Expr<?> index = ctx.accept(ExpressionVisitor.this);
                    final Expr<?> row = rowOf(primary, index, elemType);
                    if (row != null) {
                        return row;
                    }
                    primary = dereference(primary, index, elemType);
                    parseContext.getMetadata().create(primary, "cType", elemType);
                    return primary;
                } else if (arrayType instanceof CPointer) {
                    CComplexType elemType = ((CPointer) arrayType).getEmbeddedType();
                    CComplexType ptrCtype = CComplexType.getUnsignedLong(parseContext);
                    Type ptrType = ptrCtype.getSmtType();
                    Expr<?> index = ctx.accept(ExpressionVisitor.this);
                    final Expr<?> row = rowOf(primary, index, elemType);
                    if (row != null) {
                        return row;
                    }
                    if (elemType instanceof CStruct && isLiteralZero(index)) {
                        // p[0] on a pointer-to-struct IS the pointee object, and a struct's value
                        // is its base id -- so the element's value is the pointer itself. A cell
                        // read here would treat field 0's *content* as the object's base (the
                        // p->field double-deref bug, one production over). Wrap in Pos so the
                        // struct cType lands on a fresh node, not on p's shared RefExpr.
                        Expr<?> element = Pos(primary);
                        parseContext.getMetadata().create(element, "cType", elemType);
                        return element;
                    }
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
                return structMemberAccess(primary, (CStruct) type, ctx.Identifier().getText());
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
                return structMemberAccess(
                        primary, (CStruct) structTypeErased, ctx.Identifier().getText());
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
                // Post-decrement `x--` evaluates to the OLD value, exactly like `x++` returns
                // `primary` above -- the decrement is only the (post-statement) side effect. Returning
                // `expr` (= primary - 1) made `x--` yield the decremented value, so `while (n2-- != 0)`
                // read as `(n2 - 1) != 0` and ran its body once too often (at n2 == 0 it entered on
                // `-1 != 0`). That surfaced as false valid-deref alarms on the string routines
                // (`cstrncpy`, whose tail loop is `while (n2-- != 0) *us++ = 0;`).
                return primary;
            };
        }
    }
}
