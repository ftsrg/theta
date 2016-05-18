package hu.bme.mit.inf.ttmc.formalism.utils.impl;

import static com.google.common.base.Preconditions.checkState;

import hu.bme.mit.inf.ttmc.core.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.core.expr.ConstRefExpr;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.utils.impl.ExprRewriterVisitor;
import hu.bme.mit.inf.ttmc.formalism.common.decl.IndexedConstDecl;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.expr.impl.Exprs2;

public class FoldVisitor extends ExprRewriterVisitor<Integer> {

	public FoldVisitor() {
	}

	@Override
	public <DeclType extends Type> Expr<DeclType> visit(final ConstRefExpr<DeclType> expr, final Integer i) {
		final ConstDecl<DeclType> constDecl = expr.getDecl();

		if (constDecl instanceof IndexedConstDecl<?>) {
			final IndexedConstDecl<DeclType> indexedConstDecl = (IndexedConstDecl<DeclType>) constDecl;
			final int index = indexedConstDecl.getIndex();

			int nPrimes = index - i;
			checkState(nPrimes >= 0);

			final VarDecl<DeclType> varDecl = indexedConstDecl.getVarDecl();
			Expr<DeclType> res = varDecl.getRef();
			while (nPrimes > 0) {
				res = Exprs2.Prime(res);
				nPrimes--;
			}

			return res;
		} else {
			return expr;
		}

	}
}