package hu.bme.mit.inf.ttmc.formalism.utils.impl;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.inf.ttmc.formalism.common.expr.impl.Exprs2.Ref;

import hu.bme.mit.inf.ttmc.core.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.core.expr.ConstRefExpr;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.utils.impl.ExprRewriterVisitor;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.expr.impl.Exprs2;

public class FoldVisitor extends ExprRewriterVisitor<Integer> {

	final VarMap varMap;

	public FoldVisitor(final VarMap varMap) {
		this.varMap = varMap;
	}

	@Override
	public <DeclType extends Type> Expr<DeclType> visit(final ConstRefExpr<DeclType> expr, final Integer param) {
		final int i = param;
		final ConstDecl<DeclType> constDecl = expr.getDecl();
		final int index = varMap.getIndex(constDecl);

		int nPrimes = index - i;
		checkState(nPrimes >= 0);

		final VarDecl<DeclType> varDecl = varMap.getVarDecl(constDecl);
		Expr<DeclType> res = Ref(varDecl);
		while (nPrimes > 0) {
			res = Exprs2.Prime(res);
			nPrimes--;
		}

		return res;
	}
}