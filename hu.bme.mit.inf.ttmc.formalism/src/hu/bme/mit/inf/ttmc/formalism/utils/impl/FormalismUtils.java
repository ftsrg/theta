package hu.bme.mit.inf.ttmc.formalism.utils.impl;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.ExprCNFCheckerVisitor.CNFStatus;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.factory.VarDeclFactory;

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
	
	public static void collectVars(Expr<? extends Type> expr, Collection<VarDecl<? extends Type>> collectTo) {
		expr.accept(new VarCollectorVisitor(), collectTo);
	}
	
	public static CNFTransformation createCNFTransformation(ConstraintManager manager, VarDeclFactory varFactory) {
		return new CNFTransformation(manager, varFactory);
	}

}
