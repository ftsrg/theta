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
package hu.bme.mit.theta.xcfa.dsl;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.ParamDecl;
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
import hu.bme.mit.theta.xcfa.dsl.gen.XcfaDslBaseVisitor;
import hu.bme.mit.theta.xcfa.dsl.gen.XcfaDslParser;
import hu.bme.mit.theta.xcfa.dsl.gen.XcfaDslParser.*;
import org.antlr.v4.runtime.Token;

import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.stream.Stream;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.common.Utils.*;
import static hu.bme.mit.theta.core.decl.Decls.Param;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Add;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Div;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Geq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Gt;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Leq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Lt;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Mul;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neg;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Sub;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.*;
import static hu.bme.mit.theta.core.type.anytype.Exprs.Prime;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Read;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Write;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.*;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;
import static java.util.stream.Collectors.toList;

final class XcfaExpression {

	private final Scope scope;
	private final ExprContext context;

	XcfaExpression(final Scope scope, final ExprContext context) {
		this.scope = checkNotNull(scope);
		this.context = checkNotNull(context);
	}

	public Expr<?> instantiate() {
		final ExprCreatorVisitor visitor = new ExprCreatorVisitor(scope);
		final Expr<?> expr = context.accept(visitor);
		if (expr == null) {
			throw new AssertionError();
		} else {
			return expr;
		}
	}

	private static final class ExprCreatorVisitor extends XcfaDslBaseVisitor<Expr<?>> {

		private Scope currentScope;

		private ExprCreatorVisitor(final Scope scope) {
			currentScope = checkNotNull(scope);
		}

		////
/*
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
*/
		////

		@Override
		public Expr<?> visitFuncLitExpr(final FuncLitExprContext ctx) {
			if (ctx.result != null) {
				final List<ParamDecl<?>> params = createParamList(ctx.paramDecls);

				checkArgument(params.size() == 1);
				@SuppressWarnings("unchecked")
				final ParamDecl<Type> param = (ParamDecl<Type>) singleElementOf(params);

				@SuppressWarnings("unchecked")
				final Expr<Type> result = (Expr<Type>) ctx.result.accept(this);

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
						.map(d -> Param(d.name.getText(), new XcfaType(d.ttype).instantiate())).collect(toList());
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

				final Expr<BoolType> op = TypeUtils.cast(ctx.op.accept(this), Bool());

				return Forall(paramDecls, op);
			} else {
				return visitChildren(ctx);
			}
		}

		@Override
		public Expr<?> visitExistsExpr(final ExistsExprContext ctx) {
			if (ctx.paramDecls != null) {
				final List<ParamDecl<?>> paramDecls = createParamList(ctx.paramDecls);

				final Expr<BoolType> op = TypeUtils.cast(ctx.op.accept(this), Bool());

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
				case XcfaDslParser.EQ:
					return Eq(leftOp, rightOp);
				case XcfaDslParser.NEQ:
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
				case XcfaDslParser.LT:
					return Lt(leftOp, rightOp);
				case XcfaDslParser.LEQ:
					return Leq(leftOp, rightOp);
				case XcfaDslParser.GT:
					return Gt(leftOp, rightOp);
				case XcfaDslParser.GEQ:
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

			case XcfaDslParser.PLUS:
				return createAddExpr(leftOp, rightOp);

			case XcfaDslParser.MINUS:
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

			case XcfaDslParser.MUL:
				return createMulExpr(leftOp, rightOp);

			case XcfaDslParser.DIV:
				return createDivExpr(leftOp, rightOp);

			case XcfaDslParser.MOD:
				return createModExpr(leftOp, rightOp);

			case XcfaDslParser.REM:
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
			@SuppressWarnings("unchecked")
			final Expr<ArrayType<T1, T2>> array = (Expr<ArrayType<T1, T2>>) op;
			final Expr<T1> index = cast(ctx.index.accept(this), array.getType().getIndexType());
			return Read(array, index);
		}

		private <T1 extends Type, T2 extends Type> Expr<?> createArrayWriteExpr(final Expr<?> op,
				final ArrayWriteAccessContext ctx) {
			checkArgument(op.getType() instanceof ArrayType);
			@SuppressWarnings("unchecked")
			final Expr<ArrayType<T1, T2>> array = (Expr<ArrayType<T1, T2>>) op;
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
		public RefExpr<?> visitIdExpr(final IdExprContext ctx) {
			final InstantiatableSymbol symbol = (InstantiatableSymbol) currentScope.resolve(ctx.id.getText()).get();
			final Decl<?> decl = (Decl<?>) symbol.instantiate();
			return decl.getRef();
		}

		@Override
		public Expr<?> visitParenExpr(final ParenExprContext ctx) {
			return ctx.op.accept(this);
		}

	}

}
