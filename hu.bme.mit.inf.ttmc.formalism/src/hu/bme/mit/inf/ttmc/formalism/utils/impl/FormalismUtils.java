package hu.bme.mit.inf.ttmc.formalism.utils.impl;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.model.Assignment;
import hu.bme.mit.inf.ttmc.core.model.impl.AssignmentImpl;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.utils.impl.ExprCNFCheckerVisitor.CNFStatus;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;

public class FormalismUtils {

	private FormalismUtils() {
	}

	public static boolean isExprCNF(final Expr<? extends BoolType> expr) {
		return expr.accept(new FormalismCNFCheckerVisitor(), CNFStatus.START);
	}

	@SuppressWarnings("unchecked")
	public static Expr<? extends BoolType> eliminate(final Expr<? extends BoolType> expr) {
		return (Expr<? extends BoolType>) expr.accept(new FormalismITEPropagatorVisitor(new FormalismITEPusherVisitor()), null)
				.accept(new FormalismITERemoverVisitor(), null);
	}

	public static void collectVars(final Expr<? extends Type> expr, final Collection<VarDecl<? extends Type>> collectTo) {
		expr.accept(new VarCollectorVisitor(), collectTo);
	}

	public static Set<VarDecl<? extends Type>> collectVars(final Expr<? extends Type> expr) {
		final Set<VarDecl<? extends Type>> vars = new HashSet<>();
		collectVars(expr, vars);
		return vars;
	}

	public static CNFTransformation createCNFTransformation() {
		return new CNFTransformation();
	}

	public static void collectAtoms(final Expr<? extends BoolType> expr, final Collection<Expr<? extends BoolType>> collectTo) {
		expr.accept(new FormalismAtomCollectorVisitor(), collectTo);
	}

	@SuppressWarnings("unchecked")
	public static <ExprType extends Type> Expr<? extends ExprType> simplify(final Expr<? extends ExprType> expr, final Assignment assignment) {
		return (Expr<? extends ExprType>) expr.accept(new FormalismExprSimplifierVisitor(), assignment);
	}

	@SuppressWarnings("unchecked")
	public static <ExprType extends Type> Expr<? extends ExprType> simplify(final Expr<? extends ExprType> expr) {
		return (Expr<? extends ExprType>) expr.accept(new FormalismExprSimplifierVisitor(), AssignmentImpl.empty());
	}

}
