/*
 *  Copyright 2017 Budapest University of Technology and Economics
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
import static hu.bme.mit.theta.core.dsl.gen.CoreDslParser.*;
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
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Mod;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Rem;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;
import static hu.bme.mit.theta.core.utils.TypeUtils.castBv;
import static java.util.stream.Collectors.toList;

import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.stream.Stream;

import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.*;
import hu.bme.mit.theta.core.type.bvtype.BvExprs;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import org.antlr.v4.runtime.Token;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.common.dsl.BasicScope;
import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.dsl.DeclSymbol;
import hu.bme.mit.theta.core.dsl.gen.CoreDslBaseVisitor;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser;
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
import hu.bme.mit.theta.core.type.functype.FuncExprs;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.type.inttype.IntModExpr;
import hu.bme.mit.theta.core.type.inttype.IntRemExpr;
import hu.bme.mit.theta.core.type.rattype.RatLitExpr;
import hu.bme.mit.theta.core.utils.TypeUtils;

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
			@SuppressWarnings("unchecked") final ParamDecl<Type> param = (ParamDecl<Type>) singleElementOf(params);

			push(params);

			@SuppressWarnings("unchecked") final Expr<Type> result = (Expr<Type>) ctx.result.accept(this);

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
			final List<ParamDecl<?>> paramDecls = ctx.decls.stream()
					.map(d -> Param(d.name.getText(), d.ttype.accept(TypeCreatorVisitor.getInstance())))
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
			final Stream<Expr<BoolType>> opStream = ctx.ops.stream().map(op -> TypeUtils.cast(op.accept(this), Bool()));
			final Collection<Expr<BoolType>> ops = opStream.collect(toList());
			return Or(ops);
		} else {
			return visitChildren(ctx);
		}
	}

	@Override
	public Expr<?> visitAndExpr(final AndExprContext ctx) {
		if (ctx.ops.size() > 1) {
			final Stream<Expr<BoolType>> opStream = ctx.ops.stream().map(op -> TypeUtils.cast(op.accept(this), Bool()));
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
				case CoreDslParser.EQ:
					return Eq(leftOp, rightOp);
				case CoreDslParser.NEQ:
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
				case CoreDslParser.LT:
					return Lt(leftOp, rightOp);
				case CoreDslParser.LEQ:
					return Leq(leftOp, rightOp);
				case CoreDslParser.GT:
					return Gt(leftOp, rightOp);
				case CoreDslParser.GEQ:
					return Geq(leftOp, rightOp);
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
				case BITWISE_OR:
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
				case BITWISE_XOR:
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
				case BITWISE_AND:
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
				case BITWISE_SHIFT_LEFT:
					return BvExprs.ShiftLeft(leftOp, rightOp);
				case BITWISE_ARITH_SHIFT_RIGHT:
					return BvExprs.ArithShiftRight(leftOp, rightOp);
				case BITWISE_LOGIC_SHIFT_RIGHT:
					return BvExprs.LogicShiftRight(leftOp, rightOp);
				case BITWISE_ROTATE_LEFT:
					return BvExprs.RotateLeft(leftOp, rightOp);
				case BITWISE_ROTATE_RIGHT:
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

	private Expr<?> createAdditiveExpr(final Expr<?> opsHead, final List<? extends Expr<?>> opsTail,
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

	private Expr<?> createAdditiveSubExpr(final Expr<?> leftOp, final Expr<?> rightOp, final Token oper) {
		switch (oper.getType()) {

			case CoreDslParser.PLUS:
				return createAddExpr(leftOp, rightOp);

			case CoreDslParser.MINUS:
				return createSubExpr(leftOp, rightOp);

			default:
				throw new AssertionError();
		}
	}

	private AddExpr<?> createAddExpr(final Expr<?> leftOp, final Expr<?> rightOp) {
		if (leftOp instanceof AddExpr) {
			final AddExpr<?> addLeftOp = (AddExpr<?>) leftOp;
			final List<Expr<?>> ops = ImmutableList.<Expr<?>>builder().addAll(addLeftOp.getOps()).add(rightOp).build();
			return Add(ops);
		} else {
			return Add(leftOp, rightOp);
		}
	}

	private SubExpr<?> createSubExpr(final Expr<?> leftOp, final Expr<?> rightOp) {
		return Sub(leftOp, rightOp);
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

	private Expr<?> createMutliplicativeExpr(final Expr<?> opsHead, final List<? extends Expr<?>> opsTail,
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

	private Expr<?> createMultiplicativeSubExpr(final Expr<?> leftOp, final Expr<?> rightOp, final Token oper) {
		switch (oper.getType()) {

			case CoreDslParser.MUL:
				return createMulExpr(leftOp, rightOp);

			case CoreDslParser.DIV:
				return createDivExpr(leftOp, rightOp);

			case CoreDslParser.MOD:
				return createModExpr(leftOp, rightOp);

			case CoreDslParser.REM:
				return createRemExpr(leftOp, rightOp);

			default:
				throw new AssertionError();
		}
	}

	private MulExpr<?> createMulExpr(final Expr<?> leftOp, final Expr<?> rightOp) {
		if (leftOp instanceof MulExpr) {
			final MulExpr<?> addLeftOp = (MulExpr<?>) leftOp;
			final List<Expr<?>> ops = ImmutableList.<Expr<?>>builder().addAll(addLeftOp.getOps()).add(rightOp).build();
			return Mul(ops);
		} else {
			return Mul(leftOp, rightOp);
		}
	}

	private DivExpr<?> createDivExpr(final Expr<?> leftOp, final Expr<?> rightOp) {
		return Div(leftOp, rightOp);
	}

	private IntModExpr createModExpr(final Expr<?> uncastLeftOp, final Expr<?> uncastRightOp) {
		final Expr<IntType> leftOp = TypeUtils.cast(uncastLeftOp, Int());
		final Expr<IntType> rightOp = TypeUtils.cast(uncastRightOp, Int());
		return Mod(leftOp, rightOp);
	}

	private IntRemExpr createRemExpr(final Expr<?> uncastLeftOp, final Expr<?> uncastRightOp) {
		final Expr<IntType> leftOp = TypeUtils.cast(uncastLeftOp, Int());
		final Expr<IntType> rightOp = TypeUtils.cast(uncastRightOp, Int());
		return Rem(leftOp, rightOp);
	}

	////

	@Override
	public Expr<?> visitNegExpr(final NegExprContext ctx) {
		if (ctx.op != null) {
			final Expr<?> op = ctx.op.accept(this);
			return Neg(op);
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
		final int value = Integer.parseInt(ctx.value.getText());
		return Int(value);
	}

	@Override
	public RatLitExpr visitRatLitExpr(final RatLitExprContext ctx) {
		final int num = Integer.parseInt(ctx.num.getText());
		final int denom = Integer.parseInt(ctx.denom.getText());
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
