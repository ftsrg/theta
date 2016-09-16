package hu.bme.mit.theta.formalism.sts.dsl.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Add;
import static hu.bme.mit.theta.core.expr.impl.Exprs.And;
import static hu.bme.mit.theta.core.expr.impl.Exprs.App;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Eq;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Exists;
import static hu.bme.mit.theta.core.expr.impl.Exprs.False;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Forall;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Func;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Geq;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Gt;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Iff;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Imply;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Int;
import static hu.bme.mit.theta.core.expr.impl.Exprs.IntDiv;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Ite;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Leq;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Lt;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Mod;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Mul;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Neg;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Neq;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Not;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Or;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Prime;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Rat;
import static hu.bme.mit.theta.core.expr.impl.Exprs.RatDiv;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Read;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Rem;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Sub;
import static hu.bme.mit.theta.core.expr.impl.Exprs.True;
import static hu.bme.mit.theta.core.utils.impl.ExprUtils.cast;
import static java.util.stream.Collectors.toList;

import java.util.Collection;
import java.util.Collections;
import java.util.List;
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
import hu.bme.mit.theta.core.expr.AddExpr;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.FalseExpr;
import hu.bme.mit.theta.core.expr.IntDivExpr;
import hu.bme.mit.theta.core.expr.IntLitExpr;
import hu.bme.mit.theta.core.expr.ModExpr;
import hu.bme.mit.theta.core.expr.MulExpr;
import hu.bme.mit.theta.core.expr.RatDivExpr;
import hu.bme.mit.theta.core.expr.RatLitExpr;
import hu.bme.mit.theta.core.expr.RemExpr;
import hu.bme.mit.theta.core.expr.SubExpr;
import hu.bme.mit.theta.core.expr.TrueExpr;
import hu.bme.mit.theta.core.model.Assignment;
import hu.bme.mit.theta.core.type.ArrayType;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.FuncType;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.core.type.RatType;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.closure.ClosedUnderAdd;
import hu.bme.mit.theta.core.type.closure.ClosedUnderMul;
import hu.bme.mit.theta.core.type.closure.ClosedUnderNeg;
import hu.bme.mit.theta.core.type.closure.ClosedUnderSub;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslBaseVisitor;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.AccessContext;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.AccessorExprContext;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.AdditiveExprContext;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.AndExprContext;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.ArrayAccessContext;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.EqualityExprContext;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.ExistsExprContext;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.ExprListContext;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.FalseExprContext;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.ForallExprContext;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.FuncAccessContext;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.FuncLitExprContext;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.IdExprContext;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.IffExprContext;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.ImplyExprContext;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.IntLitExprContext;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.IteExprContext;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.MultiplicativeExprContext;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.NegExprContext;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.NotExprContext;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.OrExprContext;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.ParenExprContext;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.RatLitExprContext;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.RelationExprContext;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.TrueExprContext;

final class StsExprCreatorVisitor extends StsDslBaseVisitor<Expr<?>> {

	private Scope currentScope;
	private final Assignment assignment;

	StsExprCreatorVisitor(final Scope scope, final Assignment assignment) {
		currentScope = checkNotNull(scope);
		this.assignment = checkNotNull(assignment);
	}

	private void push() {
		currentScope = new BasicScope(currentScope);
	}

	private void pop() {
		checkState(currentScope.enclosingScope().isPresent());
		currentScope = currentScope.enclosingScope().get();
	}

	@Override
	public Expr<?> visitFuncLitExpr(final FuncLitExprContext ctx) {
		if (ctx.result != null) {
			final List<ParamDecl<?>> params = StsDslHelper.createParamList(ctx.paramDecls);

			checkArgument(params.size() == 1);
			@SuppressWarnings("unchecked")
			final ParamDecl<Type> param = (ParamDecl<Type>) params.get(0);

			push();

			currentScope.declare(new DeclSymbol(param));
			@SuppressWarnings("unchecked")
			final Expr<Type> result = (Expr<Type>) ctx.result.accept(this);

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
			final Expr<? extends BoolType> cond = cast(ctx.cond.accept(this), BoolType.class);
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
			final Expr<? extends BoolType> leftOp = cast(ctx.leftOp.accept(this), BoolType.class);
			final Expr<? extends BoolType> rightOp = cast(ctx.rightOp.accept(this), BoolType.class);
			return Iff(leftOp, rightOp);
		} else {
			return visitChildren(ctx);
		}
	}

	@Override
	public Expr<?> visitImplyExpr(final ImplyExprContext ctx) {
		if (ctx.rightOp != null) {
			final Expr<? extends BoolType> leftOp = cast(ctx.leftOp.accept(this), BoolType.class);
			final Expr<? extends BoolType> rightOp = cast(ctx.rightOp.accept(this), BoolType.class);
			return Imply(leftOp, rightOp);
		} else {
			return visitChildren(ctx);
		}
	}

	@Override
	public Expr<?> visitForallExpr(final ForallExprContext ctx) {
		if (ctx.paramDecls != null) {
			final List<ParamDecl<?>> paramDecls = StsDslHelper.createParamList(ctx.paramDecls);

			push();

			paramDecls.forEach(p -> currentScope.declare(new DeclSymbol(p)));
			final Expr<? extends BoolType> op = cast(ctx.op.accept(this), BoolType.class);

			pop();

			return Forall(paramDecls, op);
		} else {
			return visitChildren(ctx);
		}
	}

	@Override
	public Expr<?> visitExistsExpr(final ExistsExprContext ctx) {
		if (ctx.paramDecls != null) {
			final List<ParamDecl<?>> paramDecls = StsDslHelper.createParamList(ctx.paramDecls);

			push();

			paramDecls.forEach(p -> currentScope.declare(new DeclSymbol(p)));
			final Expr<? extends BoolType> op = cast(ctx.op.accept(this), BoolType.class);

			pop();

			return Exists(paramDecls, op);
		} else {
			return visitChildren(ctx);
		}
	}

	@Override
	public Expr<?> visitOrExpr(final OrExprContext ctx) {
		if (ctx.ops.size() > 1) {
			final Stream<Expr<? extends BoolType>> opStream = ctx.ops.stream()
					.map(op -> cast(op.accept(this), BoolType.class));
			final Collection<Expr<? extends BoolType>> ops = opStream.collect(toList());
			return Or(ops);
		} else {
			return visitChildren(ctx);
		}
	}

	@Override
	public Expr<?> visitAndExpr(final AndExprContext ctx) {
		if (ctx.ops.size() > 1) {
			final Stream<Expr<? extends BoolType>> opStream = ctx.ops.stream()
					.map(op -> cast(op.accept(this), BoolType.class));
			final Collection<Expr<? extends BoolType>> ops = opStream.collect(toList());
			return And(ops);
		} else {
			return visitChildren(ctx);
		}
	}

	@Override
	public Expr<?> visitNotExpr(final NotExprContext ctx) {
		if (ctx.op != null) {
			final Expr<? extends BoolType> op = cast(ctx.op.accept(this), BoolType.class);
			return Not(op);
		} else {
			return visitChildren(ctx);
		}
	}

	@Override
	public Expr<?> visitEqualityExpr(final EqualityExprContext ctx) {
		if (ctx.rightOp != null) {
			final Expr<? extends Type> leftOp = ctx.leftOp.accept(this);
			final Expr<? extends Type> rightOp = ctx.rightOp.accept(this);

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
			final Expr<? extends RatType> leftOp = cast(ctx.leftOp.accept(this), RatType.class);
			final Expr<? extends RatType> rightOp = cast(ctx.rightOp.accept(this), RatType.class);

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

	private AddExpr<? extends ClosedUnderAdd> createAddExpr(final Expr<?> uncastLeftOp, final Expr<?> uncastRightOp) {
		final Expr<? extends ClosedUnderAdd> leftOp = cast(uncastLeftOp, ClosedUnderAdd.class);
		final Expr<? extends ClosedUnderAdd> rightOp = cast(uncastRightOp, ClosedUnderAdd.class);

		if (leftOp instanceof AddExpr) {
			final AddExpr<? extends ClosedUnderAdd> addLeftOp = (AddExpr<? extends ClosedUnderAdd>) leftOp;
			final List<Expr<? extends ClosedUnderAdd>> ops = ImmutableList.<Expr<? extends ClosedUnderAdd>>builder()
					.addAll(addLeftOp.getOps()).add(rightOp).build();
			return Add(ops);
		} else {
			return Add(leftOp, rightOp);
		}
	}

	private SubExpr<? extends ClosedUnderSub> createSubExpr(final Expr<?> uncastLeftOp, final Expr<?> uncastRightOp) {
		final Expr<? extends ClosedUnderSub> leftOp = cast(uncastLeftOp, ClosedUnderSub.class);
		final Expr<? extends ClosedUnderSub> rightOp = cast(uncastRightOp, ClosedUnderSub.class);
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

		case StsDslParser.RDIV:
			return createRatDivExpr(leftOp, rightOp);

		case StsDslParser.IDIV:
			return createIntDivExpr(leftOp, rightOp);

		case StsDslParser.MOD:
			return createModExpr(leftOp, rightOp);

		case StsDslParser.REM:
			return createRemExpr(leftOp, rightOp);

		default:
			throw new AssertionError();
		}
	}

	private MulExpr<? extends ClosedUnderMul> createMulExpr(final Expr<?> uncastLeftOp, final Expr<?> uncastRightOp) {
		final Expr<? extends ClosedUnderMul> leftOp = cast(uncastLeftOp, ClosedUnderMul.class);
		final Expr<? extends ClosedUnderMul> rightOp = cast(uncastRightOp, ClosedUnderMul.class);

		if (leftOp instanceof MulExpr) {
			final MulExpr<? extends ClosedUnderMul> addLeftOp = (MulExpr<? extends ClosedUnderMul>) leftOp;
			final List<Expr<? extends ClosedUnderMul>> ops = ImmutableList.<Expr<? extends ClosedUnderMul>>builder()
					.addAll(addLeftOp.getOps()).add(rightOp).build();
			return Mul(ops);
		} else {
			return Mul(leftOp, rightOp);
		}
	}

	private RatDivExpr createRatDivExpr(final Expr<?> uncastLeftOp, final Expr<?> uncastRightOp) {
		final Expr<? extends IntType> leftOp = cast(uncastLeftOp, IntType.class);
		final Expr<? extends IntType> rightOp = cast(uncastRightOp, IntType.class);
		return RatDiv(leftOp, rightOp);
	}

	private IntDivExpr createIntDivExpr(final Expr<?> uncastLeftOp, final Expr<?> uncastRightOp) {
		final Expr<? extends IntType> leftOp = cast(uncastLeftOp, IntType.class);
		final Expr<? extends IntType> rightOp = cast(uncastRightOp, IntType.class);
		return IntDiv(leftOp, rightOp);
	}

	private ModExpr createModExpr(final Expr<?> uncastLeftOp, final Expr<?> uncastRightOp) {
		final Expr<? extends IntType> leftOp = cast(uncastLeftOp, IntType.class);
		final Expr<? extends IntType> rightOp = cast(uncastRightOp, IntType.class);
		return Mod(leftOp, rightOp);
	}

	private RemExpr createRemExpr(final Expr<?> uncastLeftOp, final Expr<?> uncastRightOp) {
		final Expr<? extends IntType> leftOp = cast(uncastLeftOp, IntType.class);
		final Expr<? extends IntType> rightOp = cast(uncastRightOp, IntType.class);
		return Rem(leftOp, rightOp);
	}

	////

	@Override
	public Expr<?> visitNegExpr(final NegExprContext ctx) {
		if (ctx.op != null) {
			final Expr<? extends ClosedUnderNeg> op = cast(ctx.op.accept(this), ClosedUnderNeg.class);
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
		@SuppressWarnings("unchecked")
		final Expr<? extends FuncType<Type, ?>> func = (Expr<? extends FuncType<Type, ?>>) cast(op, FuncType.class);
		final List<Expr<?>> params = createExprList(ctx.params);

		checkArgument(params.size() == 1);
		final Expr<?> param = params.get(0);

		return App(func, param);
	}

	private Expr<?> createArrayReadExpr(final Expr<?> op, final ArrayAccessContext ctx) {
		@SuppressWarnings("unchecked")
		final Expr<? extends ArrayType<Type, ?>> array = (Expr<? extends ArrayType<Type, ?>>) cast(op, ArrayType.class);
		final List<Expr<?>> indexes = createExprList(ctx.indexes);

		checkArgument(indexes.size() == 1);
		final Expr<?> index = indexes.get(0);

		return Read(array, index);
	}

	private Expr<?> createPrimeExpr(final Expr<?> op) {
		return Prime(op);
	}

	private List<Expr<?>> createExprList(final ExprListContext ctx) {
		if (ctx.exprs == null) {
			return Collections.emptyList();
		} else {
			final Stream<Expr<?>> exprStream = ctx.exprs.stream().map(e -> (Expr<?>) e.accept(this));
			final List<Expr<?>> exprs = exprStream.collect(toList());
			return exprs;
		}
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
		final long value = Long.parseLong(ctx.value.getText());
		return Int(value);
	}

	@Override
	public RatLitExpr visitRatLitExpr(final RatLitExprContext ctx) {
		final long num = Long.parseLong(ctx.num.getText());
		final long denom = Long.parseLong(ctx.denom.getText());
		return Rat(num, denom);
	}

	@Override
	public Expr<?> visitIdExpr(final IdExprContext ctx) {
		final Optional<Symbol> optSymbol = currentScope.resolve(ctx.id.getText());

		checkArgument(optSymbol.isPresent());
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
