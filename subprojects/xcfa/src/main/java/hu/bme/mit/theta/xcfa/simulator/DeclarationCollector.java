package hu.bme.mit.theta.xcfa.simulator;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.RefExpr;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

public class DeclarationCollector {

	static private void collectDeclarations(Expr<? extends Type> expr, Collection<Decl<?>> collectTo) {
		if (expr instanceof RefExpr) {
			final RefExpr<?> refExpr = (RefExpr<?>) expr;
			final Decl<?> decl = refExpr.getDecl();
			collectTo.add(decl);
		}
		expr.getOps().forEach(op -> collectDeclarations(op, collectTo));
	}

	static Set<Decl<?>> getDecls(Expr<? extends Type> expr) {
		Set<Decl<?>> x = new HashSet<>();
		collectDeclarations(expr, x);
		return x;
	}
}
