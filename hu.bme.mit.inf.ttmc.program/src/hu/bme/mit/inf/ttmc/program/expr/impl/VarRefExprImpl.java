package hu.bme.mit.inf.ttmc.program.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.expr.impl.AbstractRefExpr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;
import hu.bme.mit.inf.ttmc.program.decl.VarDecl;
import hu.bme.mit.inf.ttmc.program.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.program.expr.visitor.VarRefExprVisitor;

public final class VarRefExprImpl<DeclType extends Type>
		extends AbstractRefExpr<DeclType, VarDecl<DeclType>> implements VarRefExpr<DeclType> {
	
	public VarRefExprImpl(final VarDecl<DeclType> varDecl) {
		super(varDecl);
	}

	@Override
	protected int getHashSeed() {
		return 313;
	}
	
	@Override
	public <P, R> R accept(ExprVisitor<? super P, ? extends R> visitor, P param) {
		if (visitor instanceof VarRefExprVisitor<?, ?>) {
			final VarRefExprVisitor<? super P, ? extends R> sVisitor = (VarRefExprVisitor<? super P, ? extends R>) visitor;
			return sVisitor.visit(this, param);
		} else {
			throw new UnsupportedOperationException();
		}
	}
}
