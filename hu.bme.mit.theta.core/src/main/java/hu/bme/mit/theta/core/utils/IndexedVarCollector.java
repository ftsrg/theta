package hu.bme.mit.theta.core.utils;

import hu.bme.mit.theta.core.Decl;
import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.decl.IndexedConstDecl;
import hu.bme.mit.theta.core.type.anytype.RefExpr;

public final class IndexedVarCollector {

	private IndexedVarCollector() {
	}

	public static void collectIndexedVars(final Expr<?> expr, final IndexedVars.Builder builder) {
		if (expr instanceof RefExpr) {
			final RefExpr<?> ref = (RefExpr<?>) expr;
			final Decl<?> decl = ref.getDecl();
			if (decl instanceof IndexedConstDecl) {
				final IndexedConstDecl<?> indexedConstDecl = (IndexedConstDecl<?>) decl;
				builder.add(indexedConstDecl);
				return;
			}
		}

		expr.getOps().stream().forEach(op -> collectIndexedVars(op, builder));
	}

}
