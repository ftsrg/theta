package hu.bme.mit.inf.theta.formalism.utils;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.expr.LitExpr;
import hu.bme.mit.inf.theta.core.model.Assignment;
import hu.bme.mit.inf.theta.core.model.impl.AssignmentImpl;
import hu.bme.mit.inf.theta.core.type.BoolType;
import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.core.utils.impl.ExprCnfCheckerVisitor.CNFStatus;
import hu.bme.mit.inf.theta.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.theta.formalism.common.stmt.Stmt;
import hu.bme.mit.inf.theta.formalism.utils.impl.CnfTransformation;
import hu.bme.mit.inf.theta.formalism.utils.impl.FormalismAtomCollectorVisitor;
import hu.bme.mit.inf.theta.formalism.utils.impl.FormalismCnfCheckerVisitor;
import hu.bme.mit.inf.theta.formalism.utils.impl.FormalismExprSimplifierVisitor;
import hu.bme.mit.inf.theta.formalism.utils.impl.FormalismItePropagatorVisitor;
import hu.bme.mit.inf.theta.formalism.utils.impl.FormalismItePusherVisitor;
import hu.bme.mit.inf.theta.formalism.utils.impl.FormalismIteRemoverVisitor;

public class FormalismUtils {

	private FormalismUtils() {
	}

	public static boolean isExprCNF(final Expr<? extends BoolType> expr) {
		return expr.accept(new FormalismCnfCheckerVisitor(), CNFStatus.START);
	}

	@SuppressWarnings("unchecked")
	public static Expr<? extends BoolType> eliminate(final Expr<? extends BoolType> expr) {
		return (Expr<? extends BoolType>) expr
				.accept(new FormalismItePropagatorVisitor(new FormalismItePusherVisitor()), null)
				.accept(new FormalismIteRemoverVisitor(), null);
	}

	public static void collectVars(final Expr<?> expr, final Collection<VarDecl<? extends Type>> collectTo) {
		expr.accept(VarCollectorExprVisitor.getInstance(), collectTo);
	}

	public static Set<VarDecl<? extends Type>> getVars(final Expr<?> expr) {
		final Set<VarDecl<? extends Type>> vars = new HashSet<>();
		collectVars(expr, vars);
		return vars;
	}

	public static Set<VarDecl<? extends Type>> getVars(final Stmt stmt) {
		final Set<VarDecl<? extends Type>> vars = new HashSet<>();
		stmt.accept(VarCollectorStmtVisitor.getInstance(), vars);
		return vars;
	}

	public static CnfTransformation createCNFTransformation() {
		return new CnfTransformation();
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
