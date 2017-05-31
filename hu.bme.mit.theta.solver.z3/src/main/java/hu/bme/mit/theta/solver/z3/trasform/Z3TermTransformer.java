package hu.bme.mit.theta.solver.z3.trasform;

import static hu.bme.mit.theta.core.expr.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.expr.AbstractExprs.Geq;
import static hu.bme.mit.theta.core.expr.AbstractExprs.Gt;
import static hu.bme.mit.theta.core.expr.AbstractExprs.Leq;
import static hu.bme.mit.theta.core.expr.AbstractExprs.Lt;
import static hu.bme.mit.theta.core.expr.Exprs.Ite;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Iff;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Imply;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Add;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Div;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Mul;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Add;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Mul;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;

import java.util.LinkedList;
import java.util.List;
import java.util.concurrent.ExecutionException;

import com.google.common.cache.Cache;
import com.google.common.cache.CacheBuilder;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.IntNum;
import com.microsoft.z3.RatNum;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.ArrayType;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.core.type.RatType;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.impl.TypeUtils;

public class Z3TermTransformer {

	final Z3SymbolTable symbolTable;

	final Cache<com.microsoft.z3.Expr, Expr<?>> termToExpr;

	private static final int CACHE_SIZE = 1000;

	public Z3TermTransformer(final Z3SymbolTable symbolTable) {
		this.symbolTable = symbolTable;

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
			return True();

		} else if (term.isFalse()) {
			return False();

		} else if (term.isConst()) {
			return toConst(term);

		} else if (term.isNot()) {
			final com.microsoft.z3.Expr opTerm = term.getArgs()[0];
			final Expr<BoolType> op = TypeUtils.cast(toExpr(opTerm), BoolType.class);
			return Not(op);

		} else if (term.isOr()) {
			final com.microsoft.z3.Expr[] opTerms = term.getArgs();
			final List<Expr<BoolType>> ops = toExprListOfType(opTerms, BoolType.class);
			return Or(ops);

		} else if (term.isAnd()) {
			final com.microsoft.z3.Expr[] opTerms = term.getArgs();
			final List<Expr<BoolType>> ops = toExprListOfType(opTerms, BoolType.class);
			return And(ops);

		} else if (term.isImplies()) {
			final com.microsoft.z3.Expr leftOpTerm = term.getArgs()[0];
			final com.microsoft.z3.Expr rightOpTerm = term.getArgs()[1];
			final Expr<BoolType> leftOp = TypeUtils.cast(toExpr(leftOpTerm), BoolType.class);
			final Expr<BoolType> rightOp = TypeUtils.cast(toExpr(rightOpTerm), BoolType.class);
			return Imply(leftOp, rightOp);

		} else if (term.isIff()) {
			final com.microsoft.z3.Expr leftOpTerm = term.getArgs()[0];
			final com.microsoft.z3.Expr rightOpTerm = term.getArgs()[1];
			final Expr<BoolType> leftOp = TypeUtils.cast(toExpr(leftOpTerm), BoolType.class);
			final Expr<BoolType> rightOp = TypeUtils.cast(toExpr(rightOpTerm), BoolType.class);
			return Iff(leftOp, rightOp);

		} else if (term.isEq()) {
			final com.microsoft.z3.Expr leftOpTerm = term.getArgs()[0];
			final com.microsoft.z3.Expr rightOpTerm = term.getArgs()[1];
			final Expr<?> leftOp = toExpr(leftOpTerm);
			final Expr<?> rightOp = toExpr(rightOpTerm);
			return Eq(leftOp, rightOp);

		} else if (term.isLE()) {
			final com.microsoft.z3.Expr leftOpTerm = term.getArgs()[0];
			final com.microsoft.z3.Expr rightOpTerm = term.getArgs()[1];
			final Expr<?> leftOp = toExpr(leftOpTerm);
			final Expr<?> rightOp = toExpr(rightOpTerm);
			return Leq(leftOp, rightOp);

		} else if (term.isLT()) {
			final com.microsoft.z3.Expr leftOpTerm = term.getArgs()[0];
			final com.microsoft.z3.Expr rightOpTerm = term.getArgs()[1];
			final Expr<?> leftOp = toExpr(leftOpTerm);
			final Expr<?> rightOp = toExpr(rightOpTerm);
			return Lt(leftOp, rightOp);

		} else if (term.isGE()) {
			final com.microsoft.z3.Expr leftOpTerm = term.getArgs()[0];
			final com.microsoft.z3.Expr rightOpTerm = term.getArgs()[1];
			final Expr<?> leftOp = toExpr(leftOpTerm);
			final Expr<?> rightOp = toExpr(rightOpTerm);
			return Geq(leftOp, rightOp);

		} else if (term.isGT()) {
			final com.microsoft.z3.Expr leftOpTerm = term.getArgs()[0];
			final com.microsoft.z3.Expr rightOpTerm = term.getArgs()[1];
			final Expr<?> leftOp = toExpr(leftOpTerm);
			final Expr<?> rightOp = toExpr(rightOpTerm);
			return Gt(leftOp, rightOp);
		}

		throw new AssertionError("Unhandled case: " + term.toString());
	}

	private Expr<?> transformInt(final com.microsoft.z3.IntExpr term) {
		if (term.isIntNum()) {
			final int value = ((IntNum) term).getInt();
			return Int(value);

		} else if (term.isConst()) {
			return toConst(term);

		} else if (term.isAdd()) {
			final com.microsoft.z3.Expr[] opTerms = term.getArgs();
			final List<Expr<IntType>> ops = toExprListOfType(opTerms, IntType.class);
			return Add(ops);

		} else if (term.isMul()) {
			final com.microsoft.z3.Expr[] opTerms = term.getArgs();
			final List<Expr<IntType>> ops = toExprListOfType(opTerms, IntType.class);
			return Mul(ops);

		} else if (term.isIDiv()) {
			final com.microsoft.z3.Expr leftOpTerm = term.getArgs()[0];
			final com.microsoft.z3.Expr rightOpTerm = term.getArgs()[1];
			final Expr<IntType> leftOp = TypeUtils.cast(toExpr(leftOpTerm), IntType.class);
			final Expr<IntType> rightOp = TypeUtils.cast(toExpr(rightOpTerm), IntType.class);
			return Div(leftOp, rightOp);

		} else if (term.isITE()) {
			final com.microsoft.z3.Expr condTerm = term.getArgs()[0];
			final com.microsoft.z3.Expr thenTerm = term.getArgs()[1];
			final com.microsoft.z3.Expr elzeTerm = term.getArgs()[2];
			final Expr<BoolType> cond = TypeUtils.cast(toExpr(condTerm), BoolType.class);
			final Expr<IntType> then = TypeUtils.cast(toExpr(thenTerm), IntType.class);
			final Expr<IntType> elze = TypeUtils.cast(toExpr(elzeTerm), IntType.class);
			return Ite(cond, then, elze);
		}

		throw new AssertionError("Unhandled case: " + term.toString());
	}

	private Expr<?> transformArith(final com.microsoft.z3.ArithExpr term) {
		if (term.isRatNum()) {
			final int num = ((RatNum) term).getNumerator().getInt();
			final int denom = ((RatNum) term).getDenominator().getInt();
			return Rat(num, denom);

		} else if (term.isConst()) {
			return toConst(term);

		} else if (term.isAdd()) {
			final com.microsoft.z3.Expr[] opTerms = term.getArgs();
			final List<Expr<RatType>> ops = toExprListOfType(opTerms, RatType.class);
			return Add(ops);

		} else if (term.isMul()) {
			final com.microsoft.z3.Expr[] opTerms = term.getArgs();
			final List<Expr<RatType>> ops = toExprListOfType(opTerms, RatType.class);
			return Mul(ops);
		}

		throw new AssertionError("Unhandled case: " + term.toString());
	}

	private Expr<ArrayType<?, ?>> arrayToExpr(final com.microsoft.z3.ArrayExpr term) {
		throw new UnsupportedOperationException();
	}

	////////

	private Expr<?> toConst(final com.microsoft.z3.Expr term) {
		final FuncDecl funcDecl = term.getFuncDecl();
		final ConstDecl<?> constDecl = symbolTable.getConst(funcDecl);
		return constDecl.getRef();
	}

	private <T extends Type> List<Expr<T>> toExprListOfType(final com.microsoft.z3.Expr[] terms,
			final Class<T> metaType) {
		final List<Expr<T>> result = new LinkedList<>();
		for (final com.microsoft.z3.Expr term : terms) {
			result.add(TypeUtils.cast(toExpr(term), metaType));
		}
		return result;
	}

}
