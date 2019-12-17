package hu.bme.mit.theta.xcfa.simulator;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.RefExpr;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

/**
 * Utility function collection
 * Used for initializing the uninitialized variables in expressions:
 *   this collects all declarations used in an expressions.
 * TODO move to a util package
 */
public class DeclarationCollector {

	/**
	 * Collects all declarations referenced in an expression into a collection
	 * @param expr The expression to iterate through
	 * @param collectTo The collection to store the declarations to
	 */
	static private void collectDeclarations(Expr<? extends Type> expr, Collection<Decl<?>> collectTo) {
		if (expr instanceof RefExpr) {
			final RefExpr<?> refExpr = (RefExpr<?>) expr;
			final Decl<?> decl = refExpr.getDecl();
			collectTo.add(decl);
		}
		expr.getOps().forEach(op -> collectDeclarations(op, collectTo));
	}

	/**
	 * Collects all declarations referenced in an expression into a set
	 * @param expr The expression to iterate through
	 * @return Returns the collection of declarations in expr
	 */
	static Collection<Decl<?>> getDecls(Expr<? extends Type> expr) {
		Collection<Decl<?>> x = new HashSet<>();
		collectDeclarations(expr, x);
		return x;
	}
}
