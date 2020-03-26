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
package hu.bme.mit.theta.cfa.dsl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.*;
import static hu.bme.mit.theta.common.Utils.head;
import static hu.bme.mit.theta.common.Utils.singleElementOf;
import static hu.bme.mit.theta.common.Utils.tail;
import static hu.bme.mit.theta.core.decl.Decls.Param;
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
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Read;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Write;
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
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.Bv;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Mod;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Rem;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;
import static java.util.stream.Collectors.toList;

import java.math.BigInteger;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.stream.Stream;

import org.antlr.v4.runtime.Token;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.cfa.dsl.gen.CfaDslBaseVisitor;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.AccessContext;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.AccessorExprContext;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.AdditiveExprContext;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.AndExprContext;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.ArrayReadAccessContext;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.ArrayWriteAccessContext;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.DeclListContext;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.EqualityExprContext;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.ExistsExprContext;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.ExprContext;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.FalseExprContext;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.ForallExprContext;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.FuncAccessContext;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.FuncLitExprContext;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.IdExprContext;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.IffExprContext;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.ImplyExprContext;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.IntLitExprContext;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.IteExprContext;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.MultiplicativeExprContext;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.NegExprContext;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.NotExprContext;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.OrExprContext;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.ParenExprContext;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.RatLitExprContext;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.RelationExprContext;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.TrueExprContext;
import hu.bme.mit.theta.common.dsl.BasicScope;
import hu.bme.mit.theta.common.dsl.Env;
import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.dsl.DeclSymbol;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.abstracttype.AddExpr;
import hu.bme.mit.theta.core.type.abstracttype.DivExpr;
import hu.bme.mit.theta.core.type.abstracttype.MulExpr;
import hu.bme.mit.theta.core.type.abstracttype.SubExpr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.FalseExpr;
import hu.bme.mit.theta.core.type.booltype.TrueExpr;
import hu.bme.mit.theta.core.type.functype.FuncExprs;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.type.inttype.ModExpr;
import hu.bme.mit.theta.core.type.inttype.RemExpr;
import hu.bme.mit.theta.core.type.rattype.RatLitExpr;
import hu.bme.mit.theta.core.utils.TypeUtils;

final class CfaExpression {

	private final Scope scope;
	private final ExprContext context;

	public CfaExpression(final Scope scope, final ExprContext context) {
		this.scope = checkNotNull(scope);
		this.context = checkNotNull(context);
	}

	public Expr<?> instantiate(final Env env) {
		final ExprCreatorVisitor visitor = new ExprCreatorVisitor(scope, env);
		final Expr<?> expr = context.accept(visitor);
		if (expr == null) {
			throw new AssertionError();
		} else {
			return expr;
		}
	}

	private static final class ExprCreatorVisitor extends CfaDslBaseVisitor<Expr<?>> {

		private Scope currentScope;
		private final Env env;

		private ExprCreatorVisitor(final Scope scope, final Env env) {
			currentScope = checkNotNull(scope);
			this.env = checkNotNull(env);
		}

		////

		private void push(final List<ParamDecl<?>> paramDecls) {
			final BasicScope scope = new BasicScope(currentScope);
			env.push();
			for (final ParamDecl<?> paramDecl : paramDecls) {
				final Symbol symbol = DeclSymbol.of(paramDecl);
				scope.declare(symbol);
				env.define(symbol, paramDecl);
			}
			currentScope = scope;
		}

		private void pop() {
			checkState(currentScope.enclosingScope().isPresent(), "Enclosing scope is not present.");
			currentScope = currentScope.enclosingScope().get();
			env.pop();
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
						.map(d -> Param(d.name.getText(), new CfaType(d.ttype).instantiate())).collect(toList());
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
				final Stream<Expr<BoolType>> opStream = ctx.ops.stream()
						.map(op -> TypeUtils.cast(op.accept(this), Bool()));
				final Collection<Expr<BoolType>> ops = opStream.collect(toList());
				return Or(ops);
			} else {
				return visitChildren(ctx);
			}
		}

		@Override
		public Expr<?> visitAndExpr(final AndExprContext ctx) {
			if (ctx.ops.size() > 1) {
				final Stream<Expr<BoolType>> opStream = ctx.ops.stream()
						.map(op -> TypeUtils.cast(op.accept(this), Bool()));
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

				case PLUS:
					return createAddExpr(leftOp, rightOp);

				case MINUS:
					return createSubExpr(leftOp, rightOp);

				default:
					throw new AssertionError();
			}
		}

		private AddExpr<?> createAddExpr(final Expr<?> leftOp, final Expr<?> rightOp) {
			if (leftOp instanceof AddExpr) {
				final AddExpr<?> addLeftOp = (AddExpr<?>) leftOp;
				final List<Expr<?>> ops = ImmutableList.<Expr<?>>builder().addAll(addLeftOp.getOps()).add(rightOp)
						.build();
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

				case MUL:
					return createMulExpr(leftOp, rightOp);

				case DIV:
					return createDivExpr(leftOp, rightOp);

				case MOD:
					return createModExpr(leftOp, rightOp);

				case REM:
					return createRemExpr(leftOp, rightOp);

				default:
					throw new AssertionError();
			}
		}

		private MulExpr<?> createMulExpr(final Expr<?> leftOp, final Expr<?> rightOp) {
			if (leftOp instanceof MulExpr) {
				final MulExpr<?> addLeftOp = (MulExpr<?>) leftOp;
				final List<Expr<?>> ops = ImmutableList.<Expr<?>>builder().addAll(addLeftOp.getOps()).add(rightOp)
						.build();
				return Mul(ops);
			} else {
				return Mul(leftOp, rightOp);
			}
		}

		private DivExpr<?> createDivExpr(final Expr<?> leftOp, final Expr<?> rightOp) {
			return Div(leftOp, rightOp);
		}

		private ModExpr createModExpr(final Expr<?> uncastLeftOp, final Expr<?> uncastRightOp) {
			final Expr<IntType> leftOp = TypeUtils.cast(uncastLeftOp, Int());
			final Expr<IntType> rightOp = TypeUtils.cast(uncastRightOp, Int());
			return Mod(leftOp, rightOp);
		}

		private RemExpr createRemExpr(final Expr<?> uncastLeftOp, final Expr<?> uncastRightOp) {
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
				final AccessContext access = head(accesses);
				final Expr<?> subExpr = createAccessSubExpr(op, access);
				return createAccessExpr(subExpr, tail(accesses));
			}
		}

		private Expr<?> createAccessSubExpr(final Expr<?> op, final AccessContext access) {
			if (access.params != null) {
				return createFuncAppExpr(op, access.params);
			} else if (access.readIndex != null) {
				return createArrayReadExpr(op, access.readIndex);
			} else if (access.writeIndex != null) {
				return createArrayWriteExpr(op, access.writeIndex);
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

		private <T1 extends Type, T2 extends Type> Expr<?> createArrayReadExpr(final Expr<?> op,
																			   final ArrayReadAccessContext ctx) {
			checkArgument(op.getType() instanceof ArrayType);
			@SuppressWarnings("unchecked") final Expr<ArrayType<T1, T2>> array = (Expr<ArrayType<T1, T2>>) op;
			final Expr<T1> index = cast(ctx.index.accept(this), array.getType().getIndexType());
			return Read(array, index);
		}

		private <T1 extends Type, T2 extends Type> Expr<?> createArrayWriteExpr(final Expr<?> op,
																				final ArrayWriteAccessContext ctx) {
			checkArgument(op.getType() instanceof ArrayType);
			@SuppressWarnings("unchecked") final Expr<ArrayType<T1, T2>> array = (Expr<ArrayType<T1, T2>>) op;
			final Expr<T1> index = cast(ctx.index.accept(this), array.getType().getIndexType());
			final Expr<T2> elem = cast(ctx.elem.accept(this), array.getType().getElemType());
			return Write(array, index, elem);
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
		public Expr<?> visitBvLitExpr(final BvLitExprContext ctx) {
			final String[] sizeAndContent = ctx.bv.getText().split("'");

			final int size = Integer.parseInt(sizeAndContent[0]);
			checkArgument(size > 0, "Bitvector must have positive size");

			final boolean[] value;
			final boolean isSigned;
			if(sizeAndContent[1].startsWith("bs")) {
				value = decodeBinaryBvContent(sizeAndContent[1].substring(2));
				isSigned = true;
			}
			else if(sizeAndContent[1].startsWith("ds")) {
				value = decodeDecimalBvContent(sizeAndContent[1].substring(2), size, true);
				isSigned = true;
			}
			else if(sizeAndContent[1].startsWith("xs")) {
				value = decodeHexadecimalBvContent(sizeAndContent[1].substring(2));
				isSigned = true;
			}
			else if(sizeAndContent[1].startsWith("bu")) {
				value = decodeBinaryBvContent(sizeAndContent[1].substring(2));
				isSigned = false;
			}
			else if(sizeAndContent[1].startsWith("du")) {
				value = decodeDecimalBvContent(sizeAndContent[1].substring(2), size, false);
				isSigned = false;
			}
			else if(sizeAndContent[1].startsWith("xu")) {
				value = decodeHexadecimalBvContent(sizeAndContent[1].substring(2));
				isSigned = false;
			}
			else if(sizeAndContent[1].startsWith("b")) {
				value = decodeBinaryBvContent(sizeAndContent[1].substring(1));
				isSigned = false;
			}
			else if(sizeAndContent[1].startsWith("d")) {
				value = decodeDecimalBvContent(sizeAndContent[1].substring(1), size, false);
				isSigned = false;
			}
			else if(sizeAndContent[1].startsWith("x")) {
				value = decodeHexadecimalBvContent(sizeAndContent[1].substring(1));
				isSigned = false;
			}
			else {
				throw new IllegalArgumentException("Invalid bitvector literal");
			}

			checkArgument(value.length <= size, "The value of the literal cannot be represented on the given amount of bits");

			final boolean[] bvValue = new boolean[size];
			for(int i = 0; i < value.length; i++) {
				bvValue[size - 1 - i] = value[value.length - 1 - i];
			}

			return Bv(bvValue, isSigned);
		}

		private boolean[] decodeBinaryBvContent(String lit) {
			final boolean[] value = new boolean[lit.length()];
			for(int i = 0; i < lit.length(); i++) {
				switch (lit.toCharArray()[i]) {
					case '0': value[i] = false; break;
					case '1': value[i] = true; break;
					default: throw new IllegalArgumentException("Binary literal can contain only 0 and 1");
				}
			}
			return value;
		}

		private boolean[] decodeDecimalBvContent(String lit, int size, boolean isSigned) {
			BigInteger value = new BigInteger(lit);
			checkArgument(
				(
					isSigned &&
					value.compareTo(BigInteger.TWO.pow(size-1).multiply(BigInteger.valueOf(-1))) >= 0 &&
					value.compareTo(BigInteger.TWO.pow(size-1)) < 0
				) ||
				(
					!isSigned &&
					value.compareTo(BigInteger.ZERO) >= 0 &&
					value.compareTo(BigInteger.TWO.pow(size)) < 0
				),
				"Decimal literal is not in range"
			);

			if(isSigned && value.compareTo(BigInteger.ZERO) < 0) {
				value = value.add(BigInteger.TWO.pow(size));
			}

			return decodeBinaryBvContent(value.toString(2));
		}

		private boolean[] decodeHexadecimalBvContent(String lit) {
			final StringBuilder builder = new StringBuilder();
			for(int i = 0; i < lit.length(); i++) {
				switch (Character.toLowerCase(lit.toCharArray()[i])) {
					case '0': builder.append("0000"); break;
					case '1': builder.append("0001"); break;
					case '2': builder.append("0010"); break;
					case '3': builder.append("0011"); break;
					case '4': builder.append("0100"); break;
					case '5': builder.append("0101"); break;
					case '6': builder.append("0110"); break;
					case '7': builder.append("0111"); break;
					case '8': builder.append("1000"); break;
					case '9': builder.append("1001"); break;
					case 'a': builder.append("1010"); break;
					case 'b': builder.append("1011"); break;
					case 'c': builder.append("1100"); break;
					case 'd': builder.append("1101"); break;
					case 'e': builder.append("1110"); break;
					case 'f': builder.append("1111"); break;
					default: throw new IllegalArgumentException("Invalid hexadecimal character");
				}
			}
			return decodeBinaryBvContent(builder.toString());
		}

		@Override
		public RefExpr<?> visitIdExpr(final IdExprContext ctx) {
			final Symbol symbol = currentScope.resolve(ctx.id.getText()).get();
			final Decl<?> decl = (Decl<?>) env.eval(symbol);
			return decl.getRef();
		}

		@Override
		public Expr<?> visitParenExpr(final ParenExprContext ctx) {
			return ctx.op.accept(this);
		}

	}

}
