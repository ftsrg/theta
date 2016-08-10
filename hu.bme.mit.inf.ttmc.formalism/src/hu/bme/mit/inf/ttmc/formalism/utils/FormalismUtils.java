package hu.bme.mit.inf.ttmc.formalism.utils;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.LitExpr;
import hu.bme.mit.inf.ttmc.core.model.Assignment;
import hu.bme.mit.inf.ttmc.core.model.impl.AssignmentImpl;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.utils.impl.ExprCNFCheckerVisitor.CNFStatus;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.CNFTransformation;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.FormalismAtomCollectorVisitor;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.FormalismCNFCheckerVisitor;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.FormalismExprSimplifierVisitor;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.FormalismITEPropagatorVisitor;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.FormalismITEPusherVisitor;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.FormalismITERemoverVisitor;

public class FormalismUtils {

	private FormalismUtils() {
	}

	public static boolean isExprCNF(final Expr<? extends BoolType> expr) {
		return expr.accept(new FormalismCNFCheckerVisitor(), CNFStatus.START);
	}

	@SuppressWarnings("unchecked")
	public static Expr<? extends BoolType> eliminate(final Expr<? extends BoolType> expr) {
		return (Expr<? extends BoolType>) expr
				.accept(new FormalismITEPropagatorVisitor(new FormalismITEPusherVisitor()), null)
				.accept(new FormalismITERemoverVisitor(), null);
	}

	public static void collectVars(final Expr<?> expr,
			final Collection<VarDecl<? extends Type>> collectTo) {
		expr.accept(VarCollectorExprVisitor.getInstance(), collectTo);
	}

	public static Set<VarDecl<? extends Type>> collectVars(final Expr<?> expr) {
		final Set<VarDecl<? extends Type>> vars = new HashSet<>();
		collectVars(expr, vars);
		return vars;
	}

	public static CNFTransformation createCNFTransformation() {
		return new CNFTransformation();
	}

	public static void collectAtoms(final Expr<? extends BoolType> expr,
			final Collection<Expr<? extends BoolType>> collectTo) {
		expr.accept(new FormalismAtomCollectorVisitor(), collectTo);
	}

	@SuppressWarnings("unchecked")
	public static <ExprType extends Type> Expr<? extends ExprType> simplify(final Expr<? extends ExprType> expr,
			final Assignment assignment) {
		return (Expr<? extends ExprType>) expr.accept(new FormalismExprSimplifierVisitor(), assignment);
	}

	public static <ExprType extends Type> Expr<? extends ExprType> simplify(final Expr<? extends ExprType> expr) {
		return simplify(expr, AssignmentImpl.empty());
	}

	@SuppressWarnings("unchecked")
	public static <ExprType extends Type> LitExpr<? extends ExprType> evaluate(final Expr<? extends ExprType> expr,
			final Assignment assignment) {
		final Expr<? extends ExprType> simplified = simplify(expr, assignment);
		if (simplified instanceof LitExpr<?>) {
			return (LitExpr<ExprType>) simplified;
		} else {
			throw new RuntimeException("Could not evaluate " + expr + " with assignment " + assignment);
		}
	}

	public static <ExprType extends Type> LitExpr<? extends ExprType> evaluate(final Expr<? extends ExprType> expr) {
		return evaluate(expr, AssignmentImpl.empty());
	}
}
