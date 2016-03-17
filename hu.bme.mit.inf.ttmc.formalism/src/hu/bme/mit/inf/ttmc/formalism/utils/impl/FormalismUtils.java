package hu.bme.mit.inf.ttmc.formalism.utils.impl;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.ExprCNFCheckerVisitor.CNFStatus;

public class FormalismUtils {

	private FormalismUtils() { }
	
	public static boolean isExprCNF(Expr<? extends BoolType> expr) {
		return expr.accept(new FormalismCNFCheckerVisitor(), CNFStatus.START);
	}
	
	@SuppressWarnings("unchecked")
	public static Expr<? extends BoolType> eliminate(Expr<? extends BoolType> expr, ConstraintManager manager) {
		return (Expr<? extends BoolType>) expr.accept(
				new FormalismITEPropagatorVisitor(manager,
						new FormalismITEPusherVisitor(manager)), null).accept(
								new FormalismITERemoverVisitor(manager), null);
	}

}
