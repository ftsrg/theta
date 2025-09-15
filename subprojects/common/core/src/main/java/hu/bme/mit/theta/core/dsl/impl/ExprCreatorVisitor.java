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
package hu.bme.mit.theta.core.dsl.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.common.Utils.singleElementOf;
import static hu.bme.mit.theta.core.decl.Decls.Param;
import static hu.bme.mit.theta.core.dsl.gen.CoreDslParser.BV_ADD;
import static hu.bme.mit.theta.core.dsl.gen.CoreDslParser.BV_AND;
import static hu.bme.mit.theta.core.dsl.gen.CoreDslParser.BV_ASHR;
import static hu.bme.mit.theta.core.dsl.gen.CoreDslParser.BV_CONCAT;
import static hu.bme.mit.theta.core.dsl.gen.CoreDslParser.BV_LSHR;
import static hu.bme.mit.theta.core.dsl.gen.CoreDslParser.BV_MUL;
import static hu.bme.mit.theta.core.dsl.gen.CoreDslParser.BV_OR;
import static hu.bme.mit.theta.core.dsl.gen.CoreDslParser.BV_ROL;
import static hu.bme.mit.theta.core.dsl.gen.CoreDslParser.BV_ROR;
import static hu.bme.mit.theta.core.dsl.gen.CoreDslParser.BV_SDIV;
import static hu.bme.mit.theta.core.dsl.gen.CoreDslParser.BV_SGE;
import static hu.bme.mit.theta.core.dsl.gen.CoreDslParser.BV_SGT;
import static hu.bme.mit.theta.core.dsl.gen.CoreDslParser.BV_SHL;
import static hu.bme.mit.theta.core.dsl.gen.CoreDslParser.BV_SIGN_EXTEND;
import static hu.bme.mit.theta.core.dsl.gen.CoreDslParser.BV_SLE;
import static hu.bme.mit.theta.core.dsl.gen.CoreDslParser.BV_SLT;
import static hu.bme.mit.theta.core.dsl.gen.CoreDslParser.BV_SMOD;
import static hu.bme.mit.theta.core.dsl.gen.CoreDslParser.BV_SREM;
import static hu.bme.mit.theta.core.dsl.gen.CoreDslParser.BV_SUB;
import static hu.bme.mit.theta.core.dsl.gen.CoreDslParser.BV_UDIV;
import static hu.bme.mit.theta.core.dsl.gen.CoreDslParser.BV_UGE;
import static hu.bme.mit.theta.core.dsl.gen.CoreDslParser.BV_UGT;
import static hu.bme.mit.theta.core.dsl.gen.CoreDslParser.BV_ULE;
import static hu.bme.mit.theta.core.dsl.gen.CoreDslParser.BV_ULT;
import static hu.bme.mit.theta.core.dsl.gen.CoreDslParser.BV_UREM;
import static hu.bme.mit.theta.core.dsl.gen.CoreDslParser.BV_XOR;
import static hu.bme.mit.theta.core.dsl.gen.CoreDslParser.BV_ZERO_EXTEND;
import static hu.bme.mit.theta.core.dsl.gen.CoreDslParser.DIV;
import static hu.bme.mit.theta.core.dsl.gen.CoreDslParser.EQ;
import static hu.bme.mit.theta.core.dsl.gen.CoreDslParser.GEQ;
import static hu.bme.mit.theta.core.dsl.gen.CoreDslParser.GT;
import static hu.bme.mit.theta.core.dsl.gen.CoreDslParser.LEQ;
import static hu.bme.mit.theta.core.dsl.gen.CoreDslParser.LT;
import static hu.bme.mit.theta.core.dsl.gen.CoreDslParser.MINUS;
import static hu.bme.mit.theta.core.dsl.gen.CoreDslParser.MOD;
import static hu.bme.mit.theta.core.dsl.gen.CoreDslParser.MUL;
import static hu.bme.mit.theta.core.dsl.gen.CoreDslParser.NEQ;
import static hu.bme.mit.theta.core.dsl.gen.CoreDslParser.PLUS;
import static hu.bme.mit.theta.core.dsl.gen.CoreDslParser.REM;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Add;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Div;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Geq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Gt;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Ite;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Leq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Lt;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Mul;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neg;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Pos;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Sub;
import static hu.bme.mit.theta.core.type.anytype.Exprs.Prime;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Exists;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Forall;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Iff;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Imply;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.Extract;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.SExt;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.ZExt;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Mod;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Rem;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;
import static hu.bme.mit.theta.core.utils.TypeUtils.castBv;
import static java.util.stream.Collectors.toList;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.common.dsl.BasicScope;
import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.dsl.DeclSymbol;
import hu.bme.mit.theta.core.dsl.gen.CoreDslBaseVisitor;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.AccessContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.AccessorExprContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.AdditiveExprContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.AndExprContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.ArrayAccessContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.BitwiseAndExprContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.BitwiseOrExprContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.BitwiseShiftExprContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.BitwiseXorExprContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.BvConcatExprContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.BvExtendExprContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.BvExtractAccessContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.DeclListContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.EqualityExprContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.ExistsExprContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.FalseExprContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.ForallExprContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.FuncAccessContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.FuncLitExprContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.IdExprContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.IffExprContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.ImplyExprContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.IntLitExprContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.IteExprContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.MultiplicativeExprContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.NotExprContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.OrExprContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.ParenExprContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.RatLitExprContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.RelationExprContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.TrueExprContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.UnaryExprContext;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.abstracttype.AddExpr;
import hu.bme.mit.theta.core.type.abstracttype.DivExpr;
import hu.bme.mit.theta.core.type.abstracttype.MulExpr;
import hu.bme.mit.theta.core.type.abstracttype.SubExpr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.FalseExpr;
import hu.bme.mit.theta.core.type.booltype.TrueExpr;
import hu.bme.mit.theta.core.type.bvtype.BvAddExpr;
import hu.bme.mit.theta.core.type.bvtype.BvConcatExpr;
import hu.bme.mit.theta.core.type.bvtype.BvExprs;
import hu.bme.mit.theta.core.type.bvtype.BvMulExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSDivExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSModExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSRemExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSubExpr;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.bvtype.BvUDivExpr;
import hu.bme.mit.theta.core.type.bvtype.BvURemExpr;
import hu.bme.mit.theta.core.type.functype.FuncExprs;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntModExpr;
import hu.bme.mit.theta.core.type.inttype.IntRemExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.type.rattype.RatLitExpr;
import hu.bme.mit.theta.core.utils.TypeUtils;
import java.math.BigInteger;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.stream.Stream;
import org.antlr.v4.runtime.Token;

public final class ExprCreatorVisitor extends CoreDslBaseVisitor<Expr<?>> {

    private Scope currentScope;

    public ExprCreatorVisitor(final Scope scope) {
        this.currentScope = checkNotNull(scope);
    }

    ////

    private void push(final Collection<? extends Decl<?>> decls) {
        final BasicScope scope = new BasicScope(currentScope);
        decls.forEach(p -> scope.declare(DeclSymbol.of(p)));
        currentScope = scope;
    }

    private void pop() {
        checkState(currentScope.enclosingScope().isPresent(), "No enclosing scope is present.");
        currentScope = currentScope.enclosingScope().get();
    }

    ////

    @Override
    public Expr<?> visitFuncLitExpr(final FuncLitExprContext ctx) {
        if (ctx.result != null) {
            final List<ParamDecl<?>> params = createParamList(ctx.paramDecls);

            checkArgument(params.size() == 1);
            @SuppressWarnings("unchecked")
            final ParamDecl<Type> param = (ParamDecl<Type>) singleElementOf(params);

            push(params);

            @SuppressWarnings("unchecked")
            final Expr<Type> result = (Expr<Type>) ctx.result.accept(this);

            pop();

            return FuncExprs.Func(param, result);

        } else {
            return visitChildren(ctx);
        }
    }

    private List<ParamDecl<?>> createParamList(final DeclListContext ctx) {
        if (ctx.decls == null) {
            return Collections.emptyList();
        } else {
            final List<ParamDecl<?>> paramDecls =
                    ctx.decls.stream()
                            .map(
                                    d ->
                                            Param(
                                                    d.name.getText(),
                                                    d.ttype.accept(
                                                            TypeCreatorVisitor.getInstance())))
                            .collect(toList());
            return paramDecls;
        }
    }

    ////

    @Override
    public Expr<?> visitIteExpr(final IteExprContext ctx) {
        if (ctx.cond != null) {
            final Expr<BoolType> cond = TypeUtils.cast(ctx.cond.accept(this), Bool());
            final Expr<?> then = ctx.then.accept(this);
            final Expr<?> elze = ctx.elze.accept(this);
            return Ite(cond, then, elze);
        } else {
            return visitChildren(ctx);
        }
    }

    @Override
    public Expr<?> visitIffExpr(final IffExprContext ctx) {
        if (ctx.rightOp != null) {
            final Expr<BoolType> leftOp = TypeUtils.cast(ctx.leftOp.accept(this), Bool());
            final Expr<BoolType> rightOp = TypeUtils.cast(ctx.rightOp.accept(this), Bool());
            return Iff(leftOp, rightOp);
        } else {
            return visitChildren(ctx);
        }
    }

    @Override
    public Expr<?> visitImplyExpr(final ImplyExprContext ctx) {
        if (ctx.rightOp != null) {
            final Expr<BoolType> leftOp = TypeUtils.cast(ctx.leftOp.accept(this), Bool());
            final Expr<BoolType> rightOp = TypeUtils.cast(ctx.rightOp.accept(this), Bool());
            return Imply(leftOp, rightOp);
        } else {
            return visitChildren(ctx);
        }
    }

    @Override
    public Expr<?> visitForallExpr(final ForallExprContext ctx) {
        if (ctx.paramDecls != null) {
            final List<ParamDecl<?>> paramDecls = createParamList(ctx.paramDecls);

            push(paramDecls);
            final Expr<BoolType> op = TypeUtils.cast(ctx.op.accept(this), Bool());
            pop();

            return Forall(paramDecls, op);
        } else {
            return visitChildren(ctx);
        }
    }

    @Override
    public Expr<?> visitExistsExpr(final ExistsExprContext ctx) {
        if (ctx.paramDecls != null) {
            final List<ParamDecl<?>> paramDecls = createParamList(ctx.paramDecls);

            push(paramDecls);
            final Expr<BoolType> op = TypeUtils.cast(ctx.op.accept(this), Bool());
            pop();

            return Exists(paramDecls, op);
        } else {
            return visitChildren(ctx);
        }
    }

    @Override
    public Expr<?> visitOrExpr(final OrExprContext ctx) {
        if (ctx.ops.size() > 1) {
            final Stream<Expr<BoolType>> opStream =
                    ctx.ops.stream().map(op -> TypeUtils.cast(op.accept(this), Bool()));
            final Collection<Expr<BoolType>> ops = opStream.collect(toList());
            return Or(ops);
        } else {
            return visitChildren(ctx);
        }
    }

    @Override
    public Expr<?> visitAndExpr(final AndExprContext ctx) {
        if (ctx.ops.size() > 1) {
            final Stream<Expr<BoolType>> opStream =
                    ctx.ops.stream().map(op -> TypeUtils.cast(op.accept(this), Bool()));
            final Collection<Expr<BoolType>> ops = opStream.collect(toList());
            return And(ops);
        } else {
            return visitChildren(ctx);
        }
    }

    @Override
    public Expr<?> visitNotExpr(final NotExprContext ctx) {
        if (ctx.op != null) {
            final Expr<BoolType> op = TypeUtils.cast(ctx.op.accept(this), Bool());
            return Not(op);
        } else {
            return visitChildren(ctx);
        }
    }

    @Override
    public Expr<?> visitEqualityExpr(final EqualityExprContext ctx) {
        if (ctx.rightOp != null) {
            final Expr<?> leftOp = ctx.leftOp.accept(this);
            final Expr<?> rightOp = ctx.rightOp.accept(this);

            switch (ctx.oper.getType()) {
                case EQ:
                    return Eq(leftOp, rightOp);
                case NEQ:
                    return Neq(leftOp, rightOp);
                default:
                    throw new AssertionError();
            }

        } else {
            return visitChildren(ctx);
        }
    }

    @Override
    public Expr<?> visitRelationExpr(final RelationExprContext ctx) {
        if (ctx.rightOp != null) {
            final Expr<?> leftOp = ctx.leftOp.accept(this);
            final Expr<?> rightOp = ctx.rightOp.accept(this);

            switch (ctx.oper.getType()) {
                case LT:
                    return Lt(leftOp, rightOp);
                case LEQ:
                    return Leq(leftOp, rightOp);
                case GT:
                    return Gt(leftOp, rightOp);
                case GEQ:
                    return Geq(leftOp, rightOp);
                case BV_ULT:
                    return BvExprs.ULt(castBv(leftOp), castBv(rightOp));
                case BV_ULE:
                    return BvExprs.ULeq(castBv(leftOp), castBv(rightOp));
                case BV_UGT:
                    return BvExprs.UGt(castBv(leftOp), castBv(rightOp));
                case BV_UGE:
                    return BvExprs.UGeq(castBv(leftOp), castBv(rightOp));
                case BV_SLT:
                    return BvExprs.SLt(castBv(leftOp), castBv(rightOp));
                case BV_SLE:
                    return BvExprs.SLeq(castBv(leftOp), castBv(rightOp));
                case BV_SGT:
                    return BvExprs.SGt(castBv(leftOp), castBv(rightOp));
                case BV_SGE:
                    return BvExprs.SGeq(castBv(leftOp), castBv(rightOp));
                default:
                    throw new AssertionError();
            }

        } else {
            return visitChildren(ctx);
        }
    }

    ////

    @Override
    public Expr<?> visitBitwiseOrExpr(final BitwiseOrExprContext ctx) {
        if (ctx.rightOp != null) {
            final Expr<BvType> leftOp = castBv(ctx.leftOp.accept(this));
            final Expr<BvType> rightOp = castBv(ctx.rightOp.accept(this));

            switch (ctx.oper.getType()) {
                case BV_OR:
                    return BvExprs.Or(List.of(leftOp, rightOp));
                default:
                    throw new AssertionError();
            }

        } else {
            return visitChildren(ctx);
        }
    }

    @Override
    public Expr<?> visitBitwiseXorExpr(final BitwiseXorExprContext ctx) {
        if (ctx.rightOp != null) {
            final Expr<BvType> leftOp = castBv(ctx.leftOp.accept(this));
            final Expr<BvType> rightOp = castBv(ctx.rightOp.accept(this));

            switch (ctx.oper.getType()) {
                case BV_XOR:
                    return BvExprs.Xor(List.of(leftOp, rightOp));
                default:
                    throw new AssertionError();
            }

        } else {
            return visitChildren(ctx);
        }
    }

    @Override
    public Expr<?> visitBitwiseAndExpr(final BitwiseAndExprContext ctx) {
        if (ctx.rightOp != null) {
            final Expr<BvType> leftOp = castBv(ctx.leftOp.accept(this));
            final Expr<BvType> rightOp = castBv(ctx.rightOp.accept(this));

            switch (ctx.oper.getType()) {
                case BV_AND:
                    return BvExprs.And(List.of(leftOp, rightOp));
                default:
                    throw new AssertionError();
            }

        } else {
            return visitChildren(ctx);
        }
    }

    @Override
    public Expr<?> visitBitwiseShiftExpr(final BitwiseShiftExprContext ctx) {
        if (ctx.rightOp != null) {
            final Expr<BvType> leftOp = castBv(ctx.leftOp.accept(this));
            final Expr<BvType> rightOp = castBv(ctx.rightOp.accept(this));

            switch (ctx.oper.getType()) {
                case BV_SHL:
                    return BvExprs.ShiftLeft(leftOp, rightOp);
                case BV_ASHR:
                    return BvExprs.ArithShiftRight(leftOp, rightOp);
                case BV_LSHR:
                    return BvExprs.LogicShiftRight(leftOp, rightOp);
                case BV_ROL:
                    return BvExprs.RotateLeft(leftOp, rightOp);
                case BV_ROR:
                    return BvExprs.RotateRight(leftOp, rightOp);
                default:
                    throw new AssertionError();
            }

        } else {
            return visitChildren(ctx);
        }
    }

    ////

    @Override
    public Expr<?> visitAdditiveExpr(final AdditiveExprContext ctx) {
        if (ctx.ops.size() > 1) {
            final Stream<Expr<?>> opStream = ctx.ops.stream().map(op -> op.accept(this));
            final List<Expr<?>> ops = opStream.collect(toList());

            final Expr<?> opsHead = ops.get(0);
            final List<? extends Expr<?>> opsTail = ops.subList(1, ops.size());

            return createAdditiveExpr(opsHead, opsTail, ctx.opers);
        } else {
            return visitChildren(ctx);
        }
    }

    private Expr<?> createAdditiveExpr(
            final Expr<?> opsHead,
            final List<? extends Expr<?>> opsTail,
            final List<? extends Token> opers) {
        checkArgument(opsTail.size() == opers.size());

        if (opsTail.isEmpty()) {
            return opsHead;
        } else {
            final Expr<?> newOpsHead = opsTail.get(0);
            final List<? extends Expr<?>> newOpsTail = opsTail.subList(1, opsTail.size());

            final Token operHead = opers.get(0);
            final List<? extends Token> opersTail = opers.subList(1, opers.size());

            final Expr<?> subExpr = createAdditiveSubExpr(opsHead, newOpsHead, operHead);

            return createAdditiveExpr(subExpr, newOpsTail, opersTail);
        }
    }

    private Expr<?> createAdditiveSubExpr(
            final Expr<?> leftOp, final Expr<?> rightOp, final Token oper) {
        switch (oper.getType()) {
            case PLUS:
                return createAddExpr(leftOp, rightOp);

            case MINUS:
                return createSubExpr(leftOp, rightOp);

            case BV_ADD:
                return createBvAddExpr(castBv(leftOp), castBv(rightOp));

            case BV_SUB:
                return createBvSubExpr(castBv(leftOp), castBv(rightOp));

            default:
                throw new AssertionError();
        }
    }

    private AddExpr<?> createAddExpr(final Expr<?> leftOp, final Expr<?> rightOp) {
        if (leftOp instanceof AddExpr) {
            final AddExpr<?> addLeftOp = (AddExpr<?>) leftOp;
            final List<Expr<?>> ops =
                    ImmutableList.<Expr<?>>builder()
                            .addAll(addLeftOp.getOps())
                            .add(rightOp)
                            .build();
            return Add(ops);
        } else {
            return Add(leftOp, rightOp);
        }
    }

    private SubExpr<?> createSubExpr(final Expr<?> leftOp, final Expr<?> rightOp) {
        return Sub(leftOp, rightOp);
    }

    private BvAddExpr createBvAddExpr(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        if (leftOp instanceof BvAddExpr) {
            final BvAddExpr addLeftOp = (BvAddExpr) leftOp;
            final List<Expr<BvType>> ops =
                    ImmutableList.<Expr<BvType>>builder()
                            .addAll(addLeftOp.getOps())
                            .add(rightOp)
                            .build();
            return BvExprs.Add(ops);
        } else {
            return BvExprs.Add(Arrays.asList(leftOp, rightOp));
        }
    }

    private BvSubExpr createBvSubExpr(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        return BvExprs.Sub(leftOp, rightOp);
    }

    ////

    @Override
    public Expr<?> visitMultiplicativeExpr(final MultiplicativeExprContext ctx) {
        if (ctx.ops.size() > 1) {
            final Stream<Expr<?>> opStream = ctx.ops.stream().map(op -> op.accept(this));
            final List<Expr<?>> ops = opStream.collect(toList());

            final Expr<?> opsHead = ops.get(0);
            final List<? extends Expr<?>> opsTail = ops.subList(1, ops.size());

            return createMutliplicativeExpr(opsHead, opsTail, ctx.opers);
        } else {
            return visitChildren(ctx);
        }
    }

    private Expr<?> createMutliplicativeExpr(
            final Expr<?> opsHead,
            final List<? extends Expr<?>> opsTail,
            final List<? extends Token> opers) {
        checkArgument(opsTail.size() == opers.size());

        if (opsTail.isEmpty()) {
            return opsHead;
        } else {
            final Expr<?> newOpsHead = opsTail.get(0);
            final List<? extends Expr<?>> newOpsTail = opsTail.subList(1, opsTail.size());

            final Token operHead = opers.get(0);
            final List<? extends Token> opersTail = opers.subList(1, opers.size());

            final Expr<?> subExpr = createMultiplicativeSubExpr(opsHead, newOpsHead, operHead);

            return createMutliplicativeExpr(subExpr, newOpsTail, opersTail);
        }
    }

    private Expr<?> createMultiplicativeSubExpr(
            final Expr<?> leftOp, final Expr<?> rightOp, final Token oper) {
        switch (oper.getType()) {
            case MUL:
                return createMulExpr(leftOp, rightOp);

            case BV_MUL:
                return createBvMulExpr(castBv(leftOp), castBv(rightOp));

            case DIV:
                return createDivExpr(leftOp, rightOp);

            case BV_UDIV:
                return createBvUDivExpr(castBv(leftOp), castBv(rightOp));

            case BV_SDIV:
                return createBvSDivExpr(castBv(leftOp), castBv(rightOp));

            case MOD:
                return createModExpr(leftOp, rightOp);

            case BV_SMOD:
                return createBvSModExpr(castBv(leftOp), castBv(rightOp));

            case REM:
                return createRemExpr(leftOp, rightOp);

            case BV_UREM:
                return createBvURemExpr(castBv(leftOp), castBv(rightOp));

            case BV_SREM:
                return createBvSRemExpr(castBv(leftOp), castBv(rightOp));

            default:
                throw new AssertionError();
        }
    }

    private MulExpr<?> createMulExpr(final Expr<?> leftOp, final Expr<?> rightOp) {
        if (leftOp instanceof MulExpr) {
            final MulExpr<?> addLeftOp = (MulExpr<?>) leftOp;
            final List<Expr<?>> ops =
                    ImmutableList.<Expr<?>>builder()
                            .addAll(addLeftOp.getOps())
                            .add(rightOp)
                            .build();
            return Mul(ops);
        } else {
            return Mul(leftOp, rightOp);
        }
    }

    private BvMulExpr createBvMulExpr(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        if (leftOp instanceof BvMulExpr) {
            final BvMulExpr addLeftOp = (BvMulExpr) leftOp;
            final List<Expr<BvType>> ops =
                    ImmutableList.<Expr<BvType>>builder()
                            .addAll(addLeftOp.getOps())
                            .add(rightOp)
                            .build();
            return BvExprs.Mul(ops);
        } else {
            return BvExprs.Mul(Arrays.asList(leftOp, rightOp));
        }
    }

    private DivExpr<?> createDivExpr(final Expr<?> leftOp, final Expr<?> rightOp) {
        return Div(leftOp, rightOp);
    }

    private BvUDivExpr createBvUDivExpr(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        return BvExprs.UDiv(leftOp, rightOp);
    }

    private BvSDivExpr createBvSDivExpr(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        return BvExprs.SDiv(leftOp, rightOp);
    }

    private IntModExpr createModExpr(final Expr<?> uncastLeftOp, final Expr<?> uncastRightOp) {
        final Expr<IntType> leftOp = TypeUtils.cast(uncastLeftOp, Int());
        final Expr<IntType> rightOp = TypeUtils.cast(uncastRightOp, Int());
        return Mod(leftOp, rightOp);
    }

    private BvSModExpr createBvSModExpr(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        return BvExprs.SMod(leftOp, rightOp);
    }

    private IntRemExpr createRemExpr(final Expr<?> uncastLeftOp, final Expr<?> uncastRightOp) {
        final Expr<IntType> leftOp = TypeUtils.cast(uncastLeftOp, Int());
        final Expr<IntType> rightOp = TypeUtils.cast(uncastRightOp, Int());
        return Rem(leftOp, rightOp);
    }

    private BvURemExpr createBvURemExpr(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        return BvExprs.URem(leftOp, rightOp);
    }

    private BvSRemExpr createBvSRemExpr(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        return BvExprs.SRem(leftOp, rightOp);
    }

    ////

    @Override
    public Expr<?> visitBvConcatExpr(final BvConcatExprContext ctx) {
        if (ctx.ops.size() > 1) {
            final Stream<Expr<?>> opStream = ctx.ops.stream().map(op -> op.accept(this));
            final List<Expr<?>> ops = opStream.collect(toList());

            final Expr<?> opsHead = ops.get(0);
            final List<? extends Expr<?>> opsTail = ops.subList(1, ops.size());

            return createConcatExpr(opsHead, opsTail, ctx.opers);
        } else {
            return visitChildren(ctx);
        }
    }

    private Expr<?> createConcatExpr(
            final Expr<?> opsHead,
            final List<? extends Expr<?>> opsTail,
            final List<? extends Token> opers) {
        checkArgument(opsTail.size() == opers.size());

        if (opsTail.isEmpty()) {
            return opsHead;
        } else {
            final Expr<?> newOpsHead = opsTail.get(0);
            final List<? extends Expr<?>> newOpsTail = opsTail.subList(1, opsTail.size());

            final Token operHead = opers.get(0);
            final List<? extends Token> opersTail = opers.subList(1, opers.size());

            final Expr<?> subExpr = createConcatSubExpr(opsHead, newOpsHead, operHead);

            return createConcatExpr(subExpr, newOpsTail, opersTail);
        }
    }

    private Expr<?> createConcatSubExpr(
            final Expr<?> leftOp, final Expr<?> rightOp, final Token oper) {
        switch (oper.getType()) {
            case BV_CONCAT:
                return createBvConcatExpr(castBv(leftOp), castBv(rightOp));

            default:
                throw new AssertionError();
        }
    }

    private BvConcatExpr createBvConcatExpr(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        if (leftOp instanceof BvConcatExpr) {
            final BvConcatExpr addLeftOp = (BvConcatExpr) leftOp;
            final List<Expr<BvType>> ops =
                    ImmutableList.<Expr<BvType>>builder()
                            .addAll(addLeftOp.getOps())
                            .add(rightOp)
                            .build();
            return BvExprs.Concat(ops);
        } else {
            return BvExprs.Concat(Arrays.asList(leftOp, rightOp));
        }
    }

    @Override
    public Expr<?> visitBvExtendExpr(final BvExtendExprContext ctx) {
        if (ctx.rightOp != null) {
            final BvType extendType = BvExprs.BvType(Integer.parseInt(ctx.rightOp.size.getText()));

            switch (ctx.oper.getType()) {
                case BV_ZERO_EXTEND:
                    return ZExt(castBv(ctx.leftOp.accept(this)), extendType);

                case BV_SIGN_EXTEND:
                    return SExt(castBv(ctx.leftOp.accept(this)), extendType);

                default:
                    throw new AssertionError();
            }
        } else {
            return visitChildren(ctx);
        }
    }

    ////

    @Override
    public Expr<?> visitUnaryExpr(final UnaryExprContext ctx) {
        if (ctx.op != null) {
            final Expr<?> op = ctx.op.accept(this);
            switch (ctx.oper.getType()) {
                case PLUS:
                    return Pos(op);

                case MINUS:
                    return Neg(op);

                default:
                    throw new AssertionError();
            }
        } else {
            return visitChildren(ctx);
        }
    }

    ////

    @Override
    public Expr<?> visitAccessorExpr(final AccessorExprContext ctx) {
        if (!ctx.accesses.isEmpty()) {
            final Expr<?> op = ctx.op.accept(this);
            return createAccessExpr(op, ctx.accesses);
        } else {
            return visitChildren(ctx);
        }
    }

    private Expr<?> createAccessExpr(final Expr<?> op, final List<AccessContext> accesses) {
        if (accesses.isEmpty()) {
            return op;
        } else {
            final AccessContext access = accesses.get(0);
            final Expr<?> subExpr = createAccessSubExpr(op, access);
            return createAccessExpr(subExpr, accesses.subList(1, accesses.size()));
        }
    }

    private Expr<?> createAccessSubExpr(final Expr<?> op, final AccessContext access) {
        if (access.params != null) {
            return createFuncAppExpr(op, access.params);
        } else if (access.indexes != null) {
            return createArrayReadExpr(op, access.indexes);
        } else if (access.prime != null) {
            return createPrimeExpr(op);
        } else if (access.bvExtract != null) {
            return createBvExtractExpr(op, access.bvExtract);
        } else {
            throw new AssertionError();
        }
    }

    private Expr<?> createFuncAppExpr(final Expr<?> op, final FuncAccessContext ctx) {
        // TODO Auto-generated method stub
        throw new UnsupportedOperationException("TODO: auto-generated method stub");
    }

    private Expr<?> createArrayReadExpr(final Expr<?> op, final ArrayAccessContext ctx) {
        // TODO Auto-generated method stub
        throw new UnsupportedOperationException("TODO: auto-generated method stub");
    }

    private Expr<?> createPrimeExpr(final Expr<?> op) {
        return Prime(op);
    }

    private Expr<?> createBvExtractExpr(final Expr<?> op, final BvExtractAccessContext ctx) {
        final Expr<BvType> bitvec = castBv(op);
        return Extract(bitvec, Int(ctx.from.getText()), Int(ctx.until.getText()));
    }

    ////

    @Override
    public TrueExpr visitTrueExpr(final TrueExprContext ctx) {
        return True();
    }

    @Override
    public FalseExpr visitFalseExpr(final FalseExprContext ctx) {
        return False();
    }

    @Override
    public IntLitExpr visitIntLitExpr(final IntLitExprContext ctx) {
        final var value = new BigInteger(ctx.value.getText());
        return Int(value);
    }

    @Override
    public RatLitExpr visitRatLitExpr(final RatLitExprContext ctx) {
        final var num = new BigInteger(ctx.num.getText());
        final var denom = new BigInteger(ctx.denom.getText());
        return Rat(num, denom);
    }

    @Override
    public RefExpr<?> visitIdExpr(final IdExprContext ctx) {
        final Symbol symbol = currentScope.resolve(ctx.id.getText()).get();
        if (symbol instanceof DeclSymbol) {
            final DeclSymbol declSymbol = (DeclSymbol) symbol;
            final Decl<?> decl = declSymbol.getDecl();
            return decl.getRef();
        } else {
            throw new AssertionError();
        }
    }

    @Override
    public Expr<?> visitParenExpr(final ParenExprContext ctx) {
        return ctx.op.accept(this);
    }
}
