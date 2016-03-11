package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import hu.bme.mit.inf.ttmc.constraint.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.ConstRefExpr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public abstract class AbstractConstRefExpr<DeclType extends Type>
		extends AbstractRefExpr<DeclType, ConstDecl<DeclType>> implements ConstRefExpr<DeclType> {

	public AbstractConstRefExpr(final ConstDecl<DeclType> constDecl) {
		super(constDecl);
	}

	@Override
	protected int getHashSeed() {
		return 167;
	}
	
	@Override
	public <P, R> R accept(ExprVisitor<? super P, ? extends R> visitor, P param) {
		return visitor.visit(this, param);
	}

}
