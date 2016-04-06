package hu.bme.mit.inf.ttmc.formalism.utils.impl;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.ExprCNFCheckerVisitor.CNFStatus;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.factory.VarDeclFactory;

public class FormalismUtils {

	private FormalismUtils() {
	}

	public static boolean isExprCNF(final Expr<? extends BoolType> expr) {
		return expr.accept(new FormalismCNFCheckerVisitor(), CNFStatus.START);
	}

	@SuppressWarnings("unchecked")
	public static Expr<? extends BoolType> eliminate(final Expr<? extends BoolType> expr, final ConstraintManager manager) {
		return (Expr<? extends BoolType>) expr.accept(new FormalismITEPropagatorVisitor(manager, new FormalismITEPusherVisitor(manager)), null)
				.accept(new FormalismITERemoverVisitor(manager), null);
	}

	public static void collectVars(final Expr<? extends Type> expr, final Collection<VarDecl<? extends Type>> collectTo) {
		expr.accept(new VarCollectorVisitor(), collectTo);
	}

	public static Set<VarDecl<? extends Type>> collectVars(final Expr<? extends Type> expr) {
		final Set<VarDecl<? extends Type>> vars = new HashSet<>();
		collectVars(expr, vars);
		return vars;
	}

	public static CNFTransformation createCNFTransformation(final ConstraintManager manager, final VarDeclFactory varFactory) {
		return new CNFTransformation(manager, varFactory);
	}

	public static void collectAtoms(final Expr<? extends BoolType> expr, final Collection<Expr<? extends BoolType>> collectTo) {
		expr.accept(new FormalismAtomCollectorVisitor(), collectTo);
	}

}
