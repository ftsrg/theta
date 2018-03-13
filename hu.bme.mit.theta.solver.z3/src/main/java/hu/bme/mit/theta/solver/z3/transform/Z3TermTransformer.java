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
package hu.bme.mit.theta.solver.z3.transform;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Geq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Gt;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Leq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Lt;
import static hu.bme.mit.theta.core.type.anytype.Exprs.Ite;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
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

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.LinkedList;
import java.util.List;
import java.util.concurrent.ExecutionException;

import com.google.common.cache.Cache;
import com.google.common.cache.CacheBuilder;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.RatNum;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.type.rattype.RatType;
import hu.bme.mit.theta.core.utils.TypeUtils;

public final class Z3TermTransformer {

	private final Z3SymbolTable symbolTable;
	private final Cache<com.microsoft.z3.Expr, Expr<?>> termToExpr;

	private static final int CACHE_SIZE = 1000;

	public Z3TermTransformer(final Z3SymbolTable symbolTable) {
		this.symbolTable = symbolTable;

		termToExpr = CacheBuilder.newBuilder().maximumSize(CACHE_SIZE).build();
	}

	public Expr<?> toExpr(final com.microsoft.z3.Expr term) {
		return transform(term, new ArrayDeque<>());
	}

	////////

	private Expr<?> transform(final com.microsoft.z3.Expr term, final Deque<Decl<?>> vars) {
		try {
			return termToExpr.get(term, () -> transformTerm(term, vars));
		} catch (final ExecutionException e) {
			throw new AssertionError();
		}
	}

	private <T extends Type> List<Expr<T>> transformAll(final com.microsoft.z3.Expr[] terms, final Deque<Decl<?>> vars,
			final T type) {
		final List<Expr<T>> result = new LinkedList<>();
		for (final com.microsoft.z3.Expr term : terms) {
			result.add(TypeUtils.cast(transform(term, vars), type));
		}
		return result;
	}

	////

	private Expr<?> transformTerm(final com.microsoft.z3.Expr term, final Deque<Decl<?>> vars) {
		if (term.isIntNum()) {
			return transformIntNum(term, vars);

		} else if (term.isRatNum()) {
			return transformRatNum(term, vars);

		} else if (term.isApp()) {
			return transformApp(term, vars);

		} else if (term.isQuantifier()) {
			final com.microsoft.z3.Quantifier quantifier = (com.microsoft.z3.Quantifier) term;
			return transformQuantifier(quantifier, vars);

		} else {
			throw new AssertionError("Unhandled case: " + term.toString());
		}
	}

	private Expr<?> transformApp(final com.microsoft.z3.Expr term, final Deque<Decl<?>> vars) {
		if (term.isTrue()) {
			return transformTrue(term, vars);

		} else if (term.isFalse()) {
			return transformFalse(term, vars);

		} else if (term.isConst()) {
			return transformConst(term, vars);

		} else if (term.isNot()) {
			return transformNot(term, vars);

		} else if (term.isOr()) {
			return transformOr(term, vars);

		} else if (term.isAnd()) {
			return transformAnd(term, vars);

		} else if (term.isImplies()) {
			return transformImplies(term, vars);

		} else if (term.isIff()) {
			return transformIff(term, vars);

		} else if (term.isEq()) {
			return transformEq(term, vars);

		} else if (term.isLE()) {
			return transformLeq(term, vars);

		} else if (term.isLT()) {
			return transformLt(term, vars);

		} else if (term.isGE()) {
			return transformGeq(term, vars);

		} else if (term.isGT()) {
			return transformGt(term, vars);

		} else if (term.isAdd()) {
			return transformAdd(term, vars);

		} else if (term.isMul()) {
			return transformMul(term, vars);

		} else if (term.isIDiv()) {
			return transformIntDiv(term, vars);

		} else if (term.isITE()) {
			return transformIte(term, vars);

		} else if (term.isSelect()) {
			return transformSelect(term, vars);

		} else if (term.isStore()) {
			return transformStore(term, vars);

		} else {
			throw new AssertionError("Unhandled case: " + term.toString());
		}
	}

	private Expr<?> transformQuantifier(final com.microsoft.z3.Quantifier term, final Deque<Decl<?>> vars) {
		if (term.isUniversal()) {
			return transformUniversal(term, vars);

		} else if (term.isExistential()) {
			return transformExistential(term, vars);

		} else {
			throw new AssertionError("Unhandled case: " + term.toString());
		}
	}

	////////

	private Expr<?> transformTrue(final com.microsoft.z3.Expr term, final Deque<Decl<?>> vars) {
		return True();
	}

	private Expr<?> transformFalse(final com.microsoft.z3.Expr term, final Deque<Decl<?>> vars) {
		return False();
	}

	private Expr<?> transformIntNum(final com.microsoft.z3.Expr term, final Deque<Decl<?>> vars) {
		final int value = ((com.microsoft.z3.IntNum) term).getInt();
		return Int(value);
	}

	private Expr<?> transformRatNum(final com.microsoft.z3.Expr term, final Deque<Decl<?>> vars) {
		final int num = ((RatNum) term).getNumerator().getInt();
		final int denom = ((RatNum) term).getDenominator().getInt();
		return Rat(num, denom);
	}

	private Expr<?> transformConst(final com.microsoft.z3.Expr term, final Deque<Decl<?>> vars) {
		final FuncDecl funcDecl = term.getFuncDecl();
		final ConstDecl<?> constDecl = symbolTable.getConst(funcDecl);
		return constDecl.getRef();
	}

	private Expr<?> transformNot(final com.microsoft.z3.Expr term, final Deque<Decl<?>> vars) {
		final com.microsoft.z3.Expr opTerm = term.getArgs()[0];
		final Expr<BoolType> op = TypeUtils.cast(transform(opTerm, vars), Bool());
		return Not(op);
	}

	private Expr<?> transformOr(final com.microsoft.z3.Expr term, final Deque<Decl<?>> vars) {
		final com.microsoft.z3.Expr[] opTerms = term.getArgs();
		final List<Expr<BoolType>> ops = transformAll(opTerms, vars, Bool());
		return Or(ops);
	}

	private Expr<?> transformAnd(final com.microsoft.z3.Expr term, final Deque<Decl<?>> vars) {
		final com.microsoft.z3.Expr[] opTerms = term.getArgs();
		final List<Expr<BoolType>> ops = transformAll(opTerms, vars, Bool());
		return And(ops);
	}

	private Expr<?> transformImplies(final com.microsoft.z3.Expr term, final Deque<Decl<?>> vars) {
		final com.microsoft.z3.Expr leftOpTerm = term.getArgs()[0];
		final com.microsoft.z3.Expr rightOpTerm = term.getArgs()[1];
		final Expr<BoolType> leftOp = TypeUtils.cast(transform(leftOpTerm, vars), Bool());
		final Expr<BoolType> rightOp = TypeUtils.cast(transform(rightOpTerm, vars), Bool());
		return Imply(leftOp, rightOp);
	}

	private Expr<?> transformIff(final com.microsoft.z3.Expr term, final Deque<Decl<?>> vars) {
		final com.microsoft.z3.Expr leftOpTerm = term.getArgs()[0];
		final com.microsoft.z3.Expr rightOpTerm = term.getArgs()[1];
		final Expr<BoolType> leftOp = TypeUtils.cast(transform(leftOpTerm, vars), Bool());
		final Expr<BoolType> rightOp = TypeUtils.cast(transform(rightOpTerm, vars), Bool());
		return Iff(leftOp, rightOp);
	}

	private Expr<?> transformEq(final com.microsoft.z3.Expr term, final Deque<Decl<?>> vars) {
		final com.microsoft.z3.Expr leftOpTerm = term.getArgs()[0];
		final com.microsoft.z3.Expr rightOpTerm = term.getArgs()[1];
		final Expr<?> leftOp = transform(leftOpTerm, vars);
		final Expr<?> rightOp = transform(rightOpTerm, vars);
		return Eq(leftOp, rightOp);
	}

	private Expr<?> transformLeq(final com.microsoft.z3.Expr term, final Deque<Decl<?>> vars) {
		final com.microsoft.z3.Expr leftOpTerm = term.getArgs()[0];
		final com.microsoft.z3.Expr rightOpTerm = term.getArgs()[1];
		final Expr<?> leftOp = transform(leftOpTerm, vars);
		final Expr<?> rightOp = transform(rightOpTerm, vars);
		return Leq(leftOp, rightOp);
	}

	private Expr<?> transformLt(final com.microsoft.z3.Expr term, final Deque<Decl<?>> vars) {
		final com.microsoft.z3.Expr leftOpTerm = term.getArgs()[0];
		final com.microsoft.z3.Expr rightOpTerm = term.getArgs()[1];
		final Expr<?> leftOp = transform(leftOpTerm, vars);
		final Expr<?> rightOp = transform(rightOpTerm, vars);
		return Lt(leftOp, rightOp);
	}

	private Expr<?> transformGeq(final com.microsoft.z3.Expr term, final Deque<Decl<?>> vars) {
		final com.microsoft.z3.Expr leftOpTerm = term.getArgs()[0];
		final com.microsoft.z3.Expr rightOpTerm = term.getArgs()[1];
		final Expr<?> leftOp = transform(leftOpTerm, vars);
		final Expr<?> rightOp = transform(rightOpTerm, vars);
		return Geq(leftOp, rightOp);
	}

	private Expr<?> transformGt(final com.microsoft.z3.Expr term, final Deque<Decl<?>> vars) {
		final com.microsoft.z3.Expr leftOpTerm = term.getArgs()[0];
		final com.microsoft.z3.Expr rightOpTerm = term.getArgs()[1];
		final Expr<?> leftOp = transform(leftOpTerm, vars);
		final Expr<?> rightOp = transform(rightOpTerm, vars);
		return Gt(leftOp, rightOp);
	}

	private Expr<?> transformUniversal(final com.microsoft.z3.Expr term, final Deque<Decl<?>> vars) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	private Expr<?> transformExistential(final com.microsoft.z3.Expr term, final Deque<Decl<?>> vars) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	private Expr<?> transformAdd(final com.microsoft.z3.Expr term, final Deque<Decl<?>> vars) {
		final com.microsoft.z3.Expr[] opTerms = term.getArgs();
		if (term instanceof com.microsoft.z3.IntExpr) {
			final List<Expr<IntType>> ops = transformAll(opTerms, vars, Int());
			return Add(ops);
		} else if (term instanceof com.microsoft.z3.ArithExpr) {
			final List<Expr<RatType>> ops = transformAll(opTerms, vars, Rat());
			return Add(ops);
		} else {
			throw new UnsupportedOperationException();
		}
	}

	private Expr<?> transformMul(final com.microsoft.z3.Expr term, final Deque<Decl<?>> vars) {
		final com.microsoft.z3.Expr[] opTerms = term.getArgs();
		if (term instanceof com.microsoft.z3.IntExpr) {
			final List<Expr<IntType>> ops = transformAll(opTerms, vars, Int());
			return Mul(ops);
		} else if (term instanceof com.microsoft.z3.ArithExpr) {
			final List<Expr<RatType>> ops = transformAll(opTerms, vars, Rat());
			return Mul(ops);
		} else {
			throw new UnsupportedOperationException();
		}
	}

	private Expr<?> transformIntDiv(final com.microsoft.z3.Expr term, final Deque<Decl<?>> vars) {
		final com.microsoft.z3.Expr leftOpTerm = term.getArgs()[0];
		final com.microsoft.z3.Expr rightOpTerm = term.getArgs()[1];
		final Expr<IntType> leftOp = TypeUtils.cast(transform(leftOpTerm, vars), Int());
		final Expr<IntType> rightOp = TypeUtils.cast(transform(rightOpTerm, vars), Int());
		return Div(leftOp, rightOp);
	}

	private <T extends Type> Expr<?> transformIte(final com.microsoft.z3.Expr term, final Deque<Decl<?>> vars) {
		final com.microsoft.z3.Expr condTerm = term.getArgs()[0];
		final com.microsoft.z3.Expr thenTerm = term.getArgs()[1];
		final com.microsoft.z3.Expr elzeTerm = term.getArgs()[2];
		final Expr<BoolType> cond = TypeUtils.cast(transform(condTerm, vars), Bool());
		@SuppressWarnings("unchecked")
		final Expr<T> then = (Expr<T>) transform(thenTerm, vars);
		final Expr<T> elze = TypeUtils.cast(transform(elzeTerm, vars), then.getType());
		return Ite(cond, then, elze);
	}

	private Expr<?> transformStore(final com.microsoft.z3.Expr term, final Deque<Decl<?>> vars) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	private Expr<?> transformSelect(final com.microsoft.z3.Expr term, final Deque<Decl<?>> vars) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	private Expr<?> transformApp(final com.microsoft.z3.Expr term) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

}
