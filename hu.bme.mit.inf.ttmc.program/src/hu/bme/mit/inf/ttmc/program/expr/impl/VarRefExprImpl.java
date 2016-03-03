package hu.bme.mit.inf.ttmc.program.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.expr.impl.AbstractRefExpr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.program.decl.VarDecl;
import hu.bme.mit.inf.ttmc.program.expr.VarRefExpr;

public final class VarRefExprImpl<DeclType extends Type>
		extends AbstractRefExpr<DeclType, VarDecl<DeclType>> implements VarRefExpr<DeclType> {
	
	public VarRefExprImpl(final VarDecl<DeclType> varDecl) {
		super(varDecl);
	}

	@Override
	protected int getHashSeed() {
		return 313;
	}
	
}
