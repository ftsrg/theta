package hu.bme.mit.inf.ttmc.constraint.z3.trasform;

import java.util.LinkedList;
import java.util.List;
import java.util.concurrent.ExecutionException;

import com.google.common.cache.Cache;
import com.google.common.cache.CacheBuilder;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.IntNum;
import com.microsoft.z3.RatNum;

import hu.bme.mit.inf.ttmc.constraint.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.factory.ExprFactory;
import hu.bme.mit.inf.ttmc.constraint.type.ArrayType;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.IntType;
import hu.bme.mit.inf.ttmc.constraint.type.RatType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.ExprUtils;
import hu.bme.mit.inf.ttmc.constraint.z3.solver.Z3SymbolWrapper;

public class Z3TermToExprTransformer {

	final ExprFactory ef;
	final Z3SymbolWrapper symbolWrapper;

	final Cache<com.microsoft.z3.Expr, Expr<?>> termToExpr;

	private static final int CACHE_SIZE = 1000;

	public Z3TermToExprTransformer(final ExprFactory factory, final Z3SymbolWrapper symbolWrapper) {
		this.ef = factory;
		this.symbolWrapper = symbolWrapper;

		termToExpr = CacheBuilder.newBuilder().maximumSize(CACHE_SIZE).build();
	}

	public Expr<?> toExpr(final com.microsoft.z3.Expr term) {
		try {
			return termToExpr.get(term, (() -> transform(term)));
		} catch (final ExecutionException e) {
			throw new AssertionError();
		}
	}

	////////

	private Expr<?> transform(final com.microsoft.z3.Expr term) {
		if (term instanceof com.microsoft.z3.BoolExpr) {
			return transformBool((com.microsoft.z3.BoolExpr) term);

		} else if (term instanceof com.microsoft.z3.IntExpr) {
			return transformInt((com.microsoft.z3.IntExpr) term);

		} else if (term instanceof com.microsoft.z3.ArithExpr) {
			return transformArith((com.microsoft.z3.ArithExpr) term);

		} else if (term instanceof com.microsoft.z3.ArrayExpr) {
			return arrayToExpr((com.microsoft.z3.ArrayExpr) term);

		}

		throw new AssertionError("Unhandled case: " + term.getClass());
	}

	////////

	private Expr<?> transformBool(final com.microsoft.z3.BoolExpr term) {
		if (term.isTrue()) {
			return ef.True();

		} else if (term.isFalse()) {
			return ef.False();

		} else if (term.isConst()) {
			return toConst(term);

		} else if (term.isNot()) {
			final com.microsoft.z3.Expr opTerm = term.getArgs()[0];
			final Expr<? extends BoolType> op = ExprUtils.cast(toExpr(opTerm), BoolType.class);
			return ef.Not(op);

		} else if (term.isOr()) {
			final com.microsoft.z3.Expr[] opTerms = term.getArgs();
			final List<Expr<? extends BoolType>> ops = toExprListOfType(opTerms, BoolType.class);
			return ef.Or(ops);

		} else if (term.isAnd()) {
			final com.microsoft.z3.Expr[] opTerms = term.getArgs();
			final List<Expr<? extends BoolType>> ops = toExprListOfType(opTerms, BoolType.class);
			return ef.And(ops);

		} else if (term.isImplies()) {
			final com.microsoft.z3.Expr leftOpTerm = term.getArgs()[0];
			final com.microsoft.z3.Expr rightOpTerm = term.getArgs()[1];
			final Expr<? extends BoolType> leftOp = ExprUtils.cast(toExpr(leftOpTerm), BoolType.class);
			final Expr<? extends BoolType> rightOp = ExprUtils.cast(toExpr(rightOpTerm), BoolType.class);
			return ef.Imply(leftOp, rightOp);

		} else if (term.isIff()) {
			final com.microsoft.z3.Expr leftOpTerm = term.getArgs()[0];
			final com.microsoft.z3.Expr rightOpTerm = term.getArgs()[1];
			final Expr<? extends BoolType> leftOp = ExprUtils.cast(toExpr(leftOpTerm), BoolType.class);
			final Expr<? extends BoolType> rightOp = ExprUtils.cast(toExpr(rightOpTerm), BoolType.class);
			return ef.Iff(leftOp, rightOp);

		} else if (term.isEq()) {
			final com.microsoft.z3.Expr leftOpTerm = term.getArgs()[0];
			final com.microsoft.z3.Expr rightOpTerm = term.getArgs()[1];
			final Expr<?> leftOp = toExpr(leftOpTerm);
			final Expr<?> rightOp = toExpr(rightOpTerm);
			return ef.Eq(leftOp, rightOp);

		} else if (term.isLE()) {
			final com.microsoft.z3.Expr leftOpTerm = term.getArgs()[0];
			final com.microsoft.z3.Expr rightOpTerm = term.getArgs()[1];
			final Expr<? extends RatType> leftOp = ExprUtils.cast(toExpr(leftOpTerm), RatType.class);
			final Expr<? extends RatType> rightOp = ExprUtils.cast(toExpr(rightOpTerm), RatType.class);
			return ef.Leq(leftOp, rightOp);

		} else if (term.isLT()) {
			final com.microsoft.z3.Expr leftOpTerm = term.getArgs()[0];
			final com.microsoft.z3.Expr rightOpTerm = term.getArgs()[1];
			final Expr<? extends RatType> leftOp = ExprUtils.cast(toExpr(leftOpTerm), RatType.class);
			final Expr<? extends RatType> rightOp = ExprUtils.cast(toExpr(rightOpTerm), RatType.class);
			return ef.Lt(leftOp, rightOp);

		} else if (term.isGE()) {
			final com.microsoft.z3.Expr leftOpTerm = term.getArgs()[0];
			final com.microsoft.z3.Expr rightOpTerm = term.getArgs()[1];
			final Expr<? extends RatType> leftOp = ExprUtils.cast(toExpr(leftOpTerm), RatType.class);
			final Expr<? extends RatType> rightOp = ExprUtils.cast(toExpr(rightOpTerm), RatType.class);
			return ef.Geq(leftOp, rightOp);

		} else if (term.isGT()) {
			final com.microsoft.z3.Expr leftOpTerm = term.getArgs()[0];
			final com.microsoft.z3.Expr rightOpTerm = term.getArgs()[1];
			final Expr<? extends RatType> leftOp = ExprUtils.cast(toExpr(leftOpTerm), RatType.class);
			final Expr<? extends RatType> rightOp = ExprUtils.cast(toExpr(rightOpTerm), RatType.class);
			return ef.Gt(leftOp, rightOp);
		}

		throw new AssertionError("Unhandled case: " + term.toString());
	}

	private Expr<?> transformInt(final com.microsoft.z3.IntExpr term) {
		if (term.isIntNum()) {
			final long value = ((IntNum) term).getInt64();
			return ef.Int(value);

		} else if (term.isConst()) {
			return toConst(term);

		} else if (term.isAdd()) {
			final com.microsoft.z3.Expr[] opTerms = term.getArgs();
			final List<Expr<? extends IntType>> ops = toExprListOfType(opTerms, IntType.class);
			return ef.Add(ops);

		} else if (term.isMul()) {
			final com.microsoft.z3.Expr[] opTerms = term.getArgs();
			final List<Expr<? extends IntType>> ops = toExprListOfType(opTerms, IntType.class);
			return ef.Mul(ops);

		} else if (term.isIDiv()) {
			final com.microsoft.z3.Expr leftOpTerm = term.getArgs()[0];
			final com.microsoft.z3.Expr rightOpTerm = term.getArgs()[1];
			final Expr<? extends IntType> leftOp = ExprUtils.cast(toExpr(leftOpTerm), IntType.class);
			final Expr<? extends IntType> rightOp = ExprUtils.cast(toExpr(rightOpTerm), IntType.class);
			return ef.IntDiv(leftOp, rightOp);

		}

		throw new AssertionError("Unhandled case: " + term.toString());
	}

	private Expr<?> transformArith(final com.microsoft.z3.ArithExpr term) {
		if (term.isRatNum()) {
			final long num = ((RatNum) term).getNumerator().getInt64();
			final long denom = ((RatNum) term).getDenominator().getInt64();
			return ef.Rat(num, denom);

		} else if (term.isConst()) {
			return toConst(term);

		} else if (term.isAdd()) {
			final com.microsoft.z3.Expr[] opTerms = term.getArgs();
			final List<Expr<? extends RatType>> ops = toExprListOfType(opTerms, RatType.class);
			return ef.Add(ops);

		} else if (term.isMul()) {
			final com.microsoft.z3.Expr[] opTerms = term.getArgs();
			final List<Expr<? extends RatType>> ops = toExprListOfType(opTerms, RatType.class);
			return ef.Mul(ops);
		}

		throw new AssertionError("Unhandled case: " + term.toString());
	}

	private Expr<ArrayType<?, ?>> arrayToExpr(final com.microsoft.z3.ArrayExpr term) {
		throw new UnsupportedOperationException();
	}

	////////

	private Expr<?> toConst(final com.microsoft.z3.Expr term) {
		final FuncDecl funcDecl = term.getFuncDecl();
		final ConstDecl<?> constDecl = symbolWrapper.wrap(funcDecl);
		return ef.Ref(constDecl);
	}

	private <T extends Type> List<Expr<? extends T>> toExprListOfType(final com.microsoft.z3.Expr[] terms,
			final Class<T> metaType) {
		final List<Expr<? extends T>> result = new LinkedList<>();
		for (final com.microsoft.z3.Expr term : terms) {
			result.add(ExprUtils.cast(toExpr(term), metaType));
		}
		return result;
	}

}
