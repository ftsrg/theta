package hu.bme.mit.inf.ttmc.program.utils.impl;

import static com.google.common.base.Preconditions.checkState;

import hu.bme.mit.inf.ttmc.constraint.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.ConstRefExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.ExprRewriterVisitor;
import hu.bme.mit.inf.ttmc.program.decl.VarDecl;
import hu.bme.mit.inf.ttmc.program.factory.ProgramFactory;

class FoldVisitor extends ExprRewriterVisitor<Integer> {

	final VarMap varMap;
	final ProgramFactory factory;
	
	FoldVisitor(VarMap varMap, ProgramFactory factory) {
		this.varMap = varMap;
		this.factory = factory;
	}

	@Override
	public <DeclType extends Type> Expr<DeclType> visit(ConstRefExpr<DeclType> expr, Integer param) {
		final int i = param;
		final ConstDecl<DeclType> constDecl = expr.getDecl();
		final int index = varMap.getIndex(constDecl);
		
		int nPrimes = index - i;
		checkState(nPrimes >= 0);
		
		final VarDecl<DeclType> varDecl = varMap.getVarDecl(constDecl);
		Expr<DeclType> res = factory.Ref(varDecl);
		while (nPrimes > 0) {
			res = factory.Prime(res);
			nPrimes--;
		}
		
		return res;
	}
}
