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
import com.microsoft.z3.IntNum;
import com.microsoft.z3.Quantifier;
import com.microsoft.z3.RatNum;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.type.rattype.RatType;
import hu.bme.mit.theta.core.utils.TypeUtils;

public class Z3TermTransformer {

	final Z3SymbolTable symbolTable;

	final Cache<com.microsoft.z3.Expr, Expr<?>> termToExpr;

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
		if (term instanceof com.microsoft.z3.BoolExpr) {
			return transformBool((com.microsoft.z3.BoolExpr) term, vars);
		} else if (term instanceof com.microsoft.z3.IntExpr) {
			return transformInt((com.microsoft.z3.IntExpr) term, vars);
		} else if (term instanceof com.microsoft.z3.ArithExpr) {
			return transformArith((com.microsoft.z3.ArithExpr) term, vars);
		} else if (term instanceof com.microsoft.z3.ArrayExpr) {
			return transformArray((com.microsoft.z3.ArrayExpr) term, vars);
		} else {
			throw new AssertionError("Unhandled case: " + term.getClass());
		}
	}

	////////

	private Expr<?> transformBool(final com.microsoft.z3.BoolExpr term, final Deque<Decl<?>> vars) {
		if (term.isTrue()) {
			return True();

		} else if (term.isFalse()) {
			return False();

		} else if (term.isConst()) {
			return transformConst(term);

		} else if (term.isNot()) {
			final com.microsoft.z3.Expr opTerm = term.getArgs()[0];
			final Expr<BoolType> op = TypeUtils.cast(transform(opTerm, vars), Bool());
			return Not(op);

		} else if (term.isOr()) {
			final com.microsoft.z3.Expr[] opTerms = term.getArgs();
			final List<Expr<BoolType>> ops = transformAll(opTerms, vars, Bool());
			return Or(ops);

		} else if (term.isAnd()) {
			final com.microsoft.z3.Expr[] opTerms = term.getArgs();
			final List<Expr<BoolType>> ops = transformAll(opTerms, vars, Bool());
			return And(ops);

		} else if (term.isImplies()) {
			final com.microsoft.z3.Expr leftOpTerm = term.getArgs()[0];
			final com.microsoft.z3.Expr rightOpTerm = term.getArgs()[1];
			final Expr<BoolType> leftOp = TypeUtils.cast(transform(leftOpTerm, vars), Bool());
			final Expr<BoolType> rightOp = TypeUtils.cast(transform(rightOpTerm, vars), Bool());
			return Imply(leftOp, rightOp);

		} else if (term.isIff()) {
			final com.microsoft.z3.Expr leftOpTerm = term.getArgs()[0];
			final com.microsoft.z3.Expr rightOpTerm = term.getArgs()[1];
			final Expr<BoolType> leftOp = TypeUtils.cast(transform(leftOpTerm, vars), Bool());
			final Expr<BoolType> rightOp = TypeUtils.cast(transform(rightOpTerm, vars), Bool());
			return Iff(leftOp, rightOp);

		} else if (term.isEq()) {
			final com.microsoft.z3.Expr leftOpTerm = term.getArgs()[0];
			final com.microsoft.z3.Expr rightOpTerm = term.getArgs()[1];
			final Expr<?> leftOp = transform(leftOpTerm, vars);
			final Expr<?> rightOp = transform(rightOpTerm, vars);
			return Eq(leftOp, rightOp);

		} else if (term.isLE()) {
			final com.microsoft.z3.Expr leftOpTerm = term.getArgs()[0];
			final com.microsoft.z3.Expr rightOpTerm = term.getArgs()[1];
			final Expr<?> leftOp = transform(leftOpTerm, vars);
			final Expr<?> rightOp = transform(rightOpTerm, vars);
			return Leq(leftOp, rightOp);

		} else if (term.isLT()) {
			final com.microsoft.z3.Expr leftOpTerm = term.getArgs()[0];
			final com.microsoft.z3.Expr rightOpTerm = term.getArgs()[1];
			final Expr<?> leftOp = transform(leftOpTerm, vars);
			final Expr<?> rightOp = transform(rightOpTerm, vars);
			return Lt(leftOp, rightOp);

		} else if (term.isGE()) {
			final com.microsoft.z3.Expr leftOpTerm = term.getArgs()[0];
			final com.microsoft.z3.Expr rightOpTerm = term.getArgs()[1];
			final Expr<?> leftOp = transform(leftOpTerm, vars);
			final Expr<?> rightOp = transform(rightOpTerm, vars);
			return Geq(leftOp, rightOp);

		} else if (term.isGT()) {
			final com.microsoft.z3.Expr leftOpTerm = term.getArgs()[0];
			final com.microsoft.z3.Expr rightOpTerm = term.getArgs()[1];
			final Expr<?> leftOp = transform(leftOpTerm, vars);
			final Expr<?> rightOp = transform(rightOpTerm, vars);
			return Gt(leftOp, rightOp);

		} else if (term.isQuantifier()) {
			final com.microsoft.z3.Quantifier quantifier = (com.microsoft.z3.Quantifier) term;
			return transformQuantifier(quantifier, vars);

		} else if (term.isApp()) {
			return transformApp(term);

		} else {
			throw new AssertionError("Unhandled case: " + term.toString());
		}
	}

	private Expr<?> transformQuantifier(final Quantifier term, final Deque<Decl<?>> vars) {
		if (term.isUniversal()) {
			throw new AssertionError("Unhandled case: " + term.toString());
		} else if (term.isExistential()) {
			throw new AssertionError("Unhandled case: " + term.toString());
		} else {
			throw new AssertionError("Unhandled case: " + term.toString());
		}
	}

	private Expr<?> transformInt(final com.microsoft.z3.IntExpr term, final Deque<Decl<?>> vars) {
		if (term.isIntNum()) {
			final int value = ((IntNum) term).getInt();
			return Int(value);

		} else if (term.isConst()) {
			return transformConst(term);

		} else if (term.isAdd()) {
			final com.microsoft.z3.Expr[] opTerms = term.getArgs();
			final List<Expr<IntType>> ops = transformAll(opTerms, vars, Int());
			return Add(ops);

		} else if (term.isMul()) {
			final com.microsoft.z3.Expr[] opTerms = term.getArgs();
			final List<Expr<IntType>> ops = transformAll(opTerms, vars, Int());
			return Mul(ops);

		} else if (term.isIDiv()) {
			final com.microsoft.z3.Expr leftOpTerm = term.getArgs()[0];
			final com.microsoft.z3.Expr rightOpTerm = term.getArgs()[1];
			final Expr<IntType> leftOp = TypeUtils.cast(transform(leftOpTerm, vars), Int());
			final Expr<IntType> rightOp = TypeUtils.cast(transform(rightOpTerm, vars), Int());
			return Div(leftOp, rightOp);

		} else if (term.isITE()) {
			final com.microsoft.z3.Expr condTerm = term.getArgs()[0];
			final com.microsoft.z3.Expr thenTerm = term.getArgs()[1];
			final com.microsoft.z3.Expr elzeTerm = term.getArgs()[2];
			final Expr<BoolType> cond = TypeUtils.cast(transform(condTerm, vars), Bool());
			final Expr<IntType> then = TypeUtils.cast(transform(thenTerm, vars), Int());
			final Expr<IntType> elze = TypeUtils.cast(transform(elzeTerm, vars), Int());
			return Ite(cond, then, elze);

		} else if (term.isApp()) {
			return transformApp(term);

		} else {
			throw new AssertionError("Unhandled case: " + term.toString());
		}
	}

	private Expr<?> transformArith(final com.microsoft.z3.ArithExpr term, final Deque<Decl<?>> vars) {
		if (term.isRatNum()) {
			final int num = ((RatNum) term).getNumerator().getInt();
			final int denom = ((RatNum) term).getDenominator().getInt();
			return Rat(num, denom);

		} else if (term.isConst()) {
			return transformConst(term);

		} else if (term.isAdd()) {
			final com.microsoft.z3.Expr[] opTerms = term.getArgs();
			final List<Expr<RatType>> ops = transformAll(opTerms, vars, Rat());
			return Add(ops);

		} else if (term.isMul()) {
			final com.microsoft.z3.Expr[] opTerms = term.getArgs();
			final List<Expr<RatType>> ops = transformAll(opTerms, vars, Rat());
			return Mul(ops);

		} else if (term.isApp()) {
			return transformApp(term);

		} else {
			throw new AssertionError("Unhandled case: " + term.toString());
		}
	}

	private Expr<ArrayType<?, ?>> transformArray(final com.microsoft.z3.ArrayExpr term, final Deque<Decl<?>> vars) {
		throw new UnsupportedOperationException();
	}

	private Expr<?> transformConst(final com.microsoft.z3.Expr term) {
		final FuncDecl funcDecl = term.getFuncDecl();
		final ConstDecl<?> constDecl = symbolTable.getConst(funcDecl);
		return constDecl.getRef();
	}

	private Expr<?> transformApp(final com.microsoft.z3.Expr term) {
		throw new AssertionError("Unhandled case: " + term.toString());
	}

}
