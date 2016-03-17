package hu.bme.mit.inf.ttmc.formalism.utils.impl;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.ExprCNFCheckerVisitor.CNFStatus;

public class FormalismUtils {

	private FormalismUtils() { }
	
	public static boolean isExprCNF(Expr<? extends BoolType> expr) {
		return expr.accept(new FormalismCNFCheckerVisitor(), CNFStatus.START);
	}

}
