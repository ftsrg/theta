package hu.bme.mit.inf.ttmc.constraint.z3.solver;

import java.util.LinkedList;
import java.util.List;

import com.microsoft.z3.Context;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.IntNum;
import com.microsoft.z3.RatNum;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.solver.impl.TermWrapper;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.IntType;
import hu.bme.mit.inf.ttmc.constraint.type.RatType;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3AddExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3AndExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3ConstRefExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3EqExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3GeqExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3IffExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3IntDivExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3IntLitExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3LeqExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3MulExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3NotExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3OrExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3RatLitExpr;

public class Z3TermWrapper implements TermWrapper<com.microsoft.z3.Expr> {

	final ConstraintManager manager;
	final Context context;
	final Z3SymbolWrapper symbolWrapper;
	
	public Z3TermWrapper(final ConstraintManager manager, final Context context, final Z3SymbolWrapper symbolWrapper) {
		this.manager = manager;
		this.context = context;
		this.symbolWrapper = symbolWrapper;
	}

	@Override
	public Expr<?> wrap(com.microsoft.z3.Expr term) {

		if (term instanceof com.microsoft.z3.ArithExpr) {
			return wrapArith((com.microsoft.z3.ArithExpr) term);
		}

		if (term instanceof com.microsoft.z3.BoolExpr) {
			return wrapBool((com.microsoft.z3.BoolExpr) term);
		}

		throw new UnsupportedOperationException();
	}

	public Expr<? extends BoolType> wrapBool(com.microsoft.z3.BoolExpr term) {	
		if (term.isTrue()) {
			return manager.getExprFactory().True();
		}

		if (term.isFalse()) {
			return manager.getExprFactory().False();
		}

		if (term.isConst()) {
			final FuncDecl funcDecl = term.getFuncDecl();
			@SuppressWarnings("unchecked")
			final ConstDecl<BoolType> constDecl = (ConstDecl<BoolType>) symbolWrapper.wrap(funcDecl);
			return new Z3ConstRefExpr<>(constDecl, context);
		}

		if (term.isNot()) {
			final com.microsoft.z3.BoolExpr opTerm = (com.microsoft.z3.BoolExpr) term.getArgs()[0];
			final Expr<? extends BoolType> op = wrapBool(opTerm);
			final Expr<? extends BoolType> resExpr = new Z3NotExpr(op, context);
			return resExpr;
		}
		
		if (term.isAnd()) {
			final com.microsoft.z3.Expr[] opTerms = term.getArgs();
			final List<Expr<? extends BoolType>> ops = new LinkedList<>();
			for (com.microsoft.z3.Expr opTerm : opTerms) {
				ops.add(wrapBool((com.microsoft.z3.BoolExpr) opTerm));
			}
			
			final Expr<? extends BoolType> resExpr = new Z3AndExpr(ops, context);
			return resExpr;
		}
		
		if (term.isOr()) {
			final com.microsoft.z3.Expr[] opTerms = term.getArgs();
			final List<Expr<? extends BoolType>> ops = new LinkedList<>();
			for (com.microsoft.z3.Expr opTerm : opTerms) {
				ops.add(wrapBool((com.microsoft.z3.BoolExpr) opTerm));
			}
			
			final Expr<? extends BoolType> resExpr = new Z3OrExpr(ops, context);
			return resExpr;
		}
		
		if (term.isIff()) {
			final com.microsoft.z3.BoolExpr leftOpTerm = (com.microsoft.z3.BoolExpr) term.getArgs()[0];
			final com.microsoft.z3.BoolExpr rightOpTerm = (com.microsoft.z3.BoolExpr) term.getArgs()[1];
			final Expr<? extends BoolType> leftOp = wrapBool(leftOpTerm);
			final Expr<? extends BoolType> rightOp = wrapBool(rightOpTerm);
			
			final Expr<? extends BoolType> resExpr = new Z3IffExpr(leftOp, rightOp, context);
			return resExpr;
		}
		
		if (term.isEq()) {
			final com.microsoft.z3.Expr leftOpTerm = term.getArgs()[0];
			final com.microsoft.z3.Expr rightOpTerm = term.getArgs()[1];
			final Expr<?> leftOp = wrap(leftOpTerm);
			final Expr<?> rightOp = wrap(rightOpTerm);
			
			final Expr<? extends BoolType> resExpr = new Z3EqExpr(leftOp, rightOp, context);
			return resExpr;
		}
		
		if (term.isLE()) {
			final com.microsoft.z3.ArithExpr leftOpTerm = (com.microsoft.z3.ArithExpr) term.getArgs()[0];
			final com.microsoft.z3.ArithExpr rightOpTerm = (com.microsoft.z3.ArithExpr) term.getArgs()[1];
			final Expr<? extends RatType> leftOp = wrapArith(leftOpTerm);
			final Expr<? extends RatType> rightOp = wrapArith(rightOpTerm);
			
			final Expr<? extends BoolType> resExpr = new Z3LeqExpr(leftOp, rightOp, context);
			return resExpr;
		}
		
		if (term.isGE()) {
			final com.microsoft.z3.ArithExpr leftOpTerm = (com.microsoft.z3.ArithExpr) term.getArgs()[0];
			final com.microsoft.z3.ArithExpr rightOpTerm = (com.microsoft.z3.ArithExpr) term.getArgs()[1];
			final Expr<? extends RatType> leftOp = wrapArith(leftOpTerm);
			final Expr<? extends RatType> rightOp = wrapArith(rightOpTerm);
			
			final Expr<? extends BoolType> resExpr = new Z3GeqExpr(leftOp, rightOp, context);
			return resExpr;
		}
		
		if (term.isQuantifier()) {
			final com.microsoft.z3.Quantifier quantifier = (com.microsoft.z3.Quantifier) term;
			
			if (quantifier.isUniversal()) {
				throw new UnsupportedOperationException();
			} else if (quantifier.isExistential()) {
				throw new UnsupportedOperationException();
			}
		}

		throw new UnsupportedOperationException("Not supported: " + term);
	}

	public Expr<? extends RatType> wrapArith(com.microsoft.z3.ArithExpr term) {

		if (term.isIntNum()) {
			final long value = ((IntNum) term).getInt64();
			return new Z3IntLitExpr(value, context);
		}

		if (term.isRatNum()) {
			final long num = ((RatNum) term).getNumerator().getInt64();
			final long denom = ((RatNum) term).getDenominator().getInt64();
			return new Z3RatLitExpr(num, denom, context);
		}
		
		if (term.isConst()) {
			final FuncDecl funcDecl = term.getFuncDecl();
			final ConstDecl<?> constDecl = symbolWrapper.wrap(funcDecl);
			if (constDecl.getType() instanceof IntType) {
				@SuppressWarnings("unchecked")
				ConstDecl<IntType> intConstDecl = (ConstDecl<IntType>) constDecl;
				return new Z3ConstRefExpr<>(intConstDecl, context);
			} else if (constDecl.getType() instanceof RatType) {
				@SuppressWarnings("unchecked")
				ConstDecl<RatType> ratConstDecl = (ConstDecl<RatType>) constDecl;
				return new Z3ConstRefExpr<>(ratConstDecl, context);
			} else {
				throw new RuntimeException();
			}
		}
		
		if (term.isAdd()) {
			final com.microsoft.z3.Expr[] opTerms = term.getArgs();
			final List<Expr<? extends RatType>> ops = new LinkedList<>();
			for (com.microsoft.z3.Expr opTerm : opTerms) {
				ops.add(wrapArith((com.microsoft.z3.ArithExpr) opTerm));
			}
			
			final Expr<? extends RatType> resExpr = new Z3AddExpr<>(ops, context);
			return resExpr;
		}
		
		if (term.isMul()) {
			final com.microsoft.z3.Expr[] opTerms = term.getArgs();
			final List<Expr<? extends RatType>> ops = new LinkedList<>();
			for (com.microsoft.z3.Expr opTerm : opTerms) {
				ops.add(wrapArith((com.microsoft.z3.ArithExpr) opTerm));
			}
			
			final Expr<? extends RatType> resExpr = new Z3MulExpr<>(ops, context);
			return resExpr;
		}
		
		if (term.isIDiv()) {
			final com.microsoft.z3.ArithExpr leftOpTerm = (com.microsoft.z3.ArithExpr) term.getArgs()[0];
			final com.microsoft.z3.ArithExpr rightOpTerm = (com.microsoft.z3.ArithExpr) term.getArgs()[1];
			@SuppressWarnings("unchecked")
			final Expr<? extends IntType> leftOp = (Expr<? extends IntType>) wrapArith(leftOpTerm);
			@SuppressWarnings("unchecked")
			final Expr<? extends IntType> rightOp = (Expr<? extends IntType>) wrapArith(rightOpTerm);
			
			final Expr<? extends IntType> resExpr = new Z3IntDivExpr(leftOp, rightOp, context);
			return resExpr;
		}

		throw new UnsupportedOperationException("Not supported: " + term);
	}
	
}
