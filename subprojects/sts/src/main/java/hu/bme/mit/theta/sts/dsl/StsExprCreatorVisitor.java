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
package hu.bme.mit.theta.sts.dsl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.common.Utils.singleElementOf;
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
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;
import static hu.bme.mit.theta.core.type.functype.FuncExprs.Func;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Mod;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Rem;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;
import static hu.bme.mit.theta.sts.dsl.StsDslHelper.createParamList;
import static java.util.stream.Collectors.toList;

import java.math.BigInteger;
import java.util.Collection;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.Optional;
import java.util.stream.Stream;

import org.antlr.v4.runtime.Token;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.common.dsl.BasicScope;
import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.dsl.DeclSymbol;
import hu.bme.mit.theta.core.model.Substitution;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.abstracttype.AddExpr;
import hu.bme.mit.theta.core.type.abstracttype.DivExpr;
import hu.bme.mit.theta.core.type.abstracttype.MulExpr;
import hu.bme.mit.theta.core.type.abstracttype.SubExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.FalseExpr;
import hu.bme.mit.theta.core.type.booltype.TrueExpr;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.type.inttype.IntModExpr;
import hu.bme.mit.theta.core.type.inttype.IntRemExpr;
import hu.bme.mit.theta.core.type.rattype.RatLitExpr;
import hu.bme.mit.theta.core.utils.TypeUtils;
import hu.bme.mit.theta.sts.dsl.gen.StsDslBaseVisitor;
import hu.bme.mit.theta.sts.dsl.gen.StsDslParser;
import hu.bme.mit.theta.sts.dsl.gen.StsDslParser.AccessContext;
import hu.bme.mit.theta.sts.dsl.gen.StsDslParser.AccessorExprContext;
import hu.bme.mit.theta.sts.dsl.gen.StsDslParser.AdditiveExprContext;
import hu.bme.mit.theta.sts.dsl.gen.StsDslParser.AndExprContext;
import hu.bme.mit.theta.sts.dsl.gen.StsDslParser.ArrayAccessContext;
import hu.bme.mit.theta.sts.dsl.gen.StsDslParser.EqualityExprContext;
import hu.bme.mit.theta.sts.dsl.gen.StsDslParser.ExistsExprContext;
import hu.bme.mit.theta.sts.dsl.gen.StsDslParser.FalseExprContext;
import hu.bme.mit.theta.sts.dsl.gen.StsDslParser.ForallExprContext;
import hu.bme.mit.theta.sts.dsl.gen.StsDslParser.FuncAccessContext;
import hu.bme.mit.theta.sts.dsl.gen.StsDslParser.FuncLitExprContext;
import hu.bme.mit.theta.sts.dsl.gen.StsDslParser.IdExprContext;
import hu.bme.mit.theta.sts.dsl.gen.StsDslParser.IffExprContext;
import hu.bme.mit.theta.sts.dsl.gen.StsDslParser.ImplyExprContext;
import hu.bme.mit.theta.sts.dsl.gen.StsDslParser.IntLitExprContext;
import hu.bme.mit.theta.sts.dsl.gen.StsDslParser.IteExprContext;
import hu.bme.mit.theta.sts.dsl.gen.StsDslParser.MultiplicativeExprContext;
import hu.bme.mit.theta.sts.dsl.gen.StsDslParser.NegExprContext;
import hu.bme.mit.theta.sts.dsl.gen.StsDslParser.NotExprContext;
import hu.bme.mit.theta.sts.dsl.gen.StsDslParser.OrExprContext;
import hu.bme.mit.theta.sts.dsl.gen.StsDslParser.ParenExprContext;
import hu.bme.mit.theta.sts.dsl.gen.StsDslParser.RatLitExprContext;
import hu.bme.mit.theta.sts.dsl.gen.StsDslParser.RelationExprContext;
import hu.bme.mit.theta.sts.dsl.gen.StsDslParser.TrueExprContext;
import hu.bme.mit.theta.sts.dsl.gen.StsDslParser.XorExprContext;

final class StsExprCreatorVisitor extends StsDslBaseVisitor<Expr<?>> {

	private Scope currentScope;
	private final Substitution assignment;

	StsExprCreatorVisitor(final Scope scope, final Substitution assignment) {
		currentScope = checkNotNull(scope);
		this.assignment = checkNotNull(assignment);
	}

	////

	private void push(final Collection<? extends Decl<?>> decls) {
		final BasicScope scope = new BasicScope(currentScope);
		decls.forEach(p -> scope.declare(DeclSymbol.of(p)));
		currentScope = scope;
	}

	private void pop() {
		checkState(currentScope.enclosingScope().isPresent(), "Enclosing scope is not present.");
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

			return Func(param, result);
		} else {
			return visitChildren(ctx);
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
	public Expr<?> visitXorExpr(final XorExprContext ctx) {
		if (ctx.rightOp != null) {
			final Expr<BoolType> leftOp = TypeUtils.cast(ctx.leftOp.accept(this), Bool());
			final Expr<BoolType> rightOp = TypeUtils.cast(ctx.rightOp.accept(this), Bool());
			return Xor(leftOp, rightOp);
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
				case StsDslParser.EQ:
					return Eq(leftOp, rightOp);
				case StsDslParser.NEQ:
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
				case StsDslParser.LT:
					return Lt(leftOp, rightOp);
				case StsDslParser.LEQ:
					return Leq(leftOp, rightOp);
				case StsDslParser.GT:
					return Gt(leftOp, rightOp);
				case StsDslParser.GEQ:
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

			case StsDslParser.PLUS:
				return createAddExpr(leftOp, rightOp);

			case StsDslParser.MINUS:
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

			case StsDslParser.MUL:
				return createMulExpr(leftOp, rightOp);

			case StsDslParser.DIV:
				return createDivExpr(leftOp, rightOp);

			case StsDslParser.MOD:
				return createModExpr(leftOp, rightOp);

			case StsDslParser.REM:
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
	public Expr<?> visitIdExpr(final IdExprContext ctx) {
		final Optional<? extends Symbol> optSymbol = currentScope.resolve(ctx.id.getText());

		if (optSymbol.isEmpty()) throw new NoSuchElementException("Identifier '" + ctx.id.getText() + "' not found");
		final Symbol symbol = optSymbol.get();

		checkArgument(symbol instanceof DeclSymbol);
		final DeclSymbol declSymbol = (DeclSymbol) symbol;
		final Decl<?> decl = declSymbol.getDecl();

		final Optional<? extends Expr<?>> optValue = assignment.eval(decl);
		if (optValue.isPresent()) {
			return optValue.get();
		} else {
			return decl.getRef();
		}

	}

	@Override
	public Expr<?> visitParenExpr(final ParenExprContext ctx) {
		return ctx.op.accept(this);
	}

}
