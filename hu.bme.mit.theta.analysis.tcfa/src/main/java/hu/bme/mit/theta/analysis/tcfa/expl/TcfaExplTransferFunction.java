package hu.bme.mit.theta.analysis.tcfa.expl;

import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.tcfa.TcfaAction;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.BoolLitExpr;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.LitExpr;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.impl.ExprUtils;
import hu.bme.mit.theta.formalism.ta.utils.impl.TaStmt;

final class TcfaExplTransferFunction implements TransferFunction<ExplState, TcfaAction, ExplPrec> {

	private static final TcfaExplTransferFunction INSTANCE = new TcfaExplTransferFunction();

	private TcfaExplTransferFunction() {
	}

	public static TcfaExplTransferFunction getInstance() {
		return INSTANCE;
	}

	@Override
	public Collection<? extends ExplState> getSuccStates(final ExplState state, final TcfaAction action,
			final ExplPrec prec) {

		Valuation currentValuation = state.getValuation();

		for (final TaStmt tcfaStmt : action.getTcfaStmts()) {

			if (tcfaStmt.isDataStmt()) {
				final Stmt stmt = tcfaStmt.getStmt();

				if (stmt instanceof AssumeStmt) {
					final AssumeStmt assumeStmt = (AssumeStmt) stmt;
					final Expr<? extends BoolType> cond = assumeStmt.getCond();
					final LitExpr<? extends BoolType> evaledCond = ExprUtils.evaluate(cond, currentValuation);
					if (evaledCond instanceof BoolLitExpr) {
						final BoolLitExpr boolResult = (BoolLitExpr) evaledCond;
						if (!boolResult.getValue()) {
							return Collections.emptySet();
						}
					} else {
						throw new AssertionError();
					}

				} else if (stmt instanceof AssignStmt) {
					@SuppressWarnings("unchecked")
					final AssignStmt<Type, Type> assignStmt = (AssignStmt<Type, Type>) stmt;
					final VarDecl<Type> varDecl = assignStmt.getVarDecl();
					// TODO Check if prec contains varDecl
					final Expr<Type> expr = assignStmt.getExpr();
					final LitExpr<? extends Type> evaledExpr = ExprUtils.evaluate(expr, currentValuation);
					final Valuation newValuation = currentValuation.transform().put(varDecl, evaledExpr).build();
					currentValuation = newValuation;
				}
			}
		}

		final ExplState newState = ExplState.create(currentValuation);
		return Collections.singleton(newState);
	}

}
