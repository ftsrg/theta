package hu.bme.mit.inf.ttmc.constraint.decl.defaults;

import hu.bme.mit.inf.ttmc.constraint.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.ConstRefExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.ConstRefExprImpl;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public abstract class AbstractConstDecl<DeclType extends Type> extends AbstractDecl<DeclType> implements ConstDecl<DeclType> {
	
	protected volatile ConstRefExpr<DeclType> ref;
	
	public AbstractConstDecl(final String name, final DeclType type) {
		super(name, type);
	}
	
	@Override
	public ConstRefExpr<DeclType> getRef() {
		if (ref == null) {
			ref = new ConstRefExprImpl<>(this);
		}
		
		return ref;
	}
	
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Const(");
		sb.append(getName());
		sb.append(" : ");
		sb.append(getType());
		sb.append(")");
		return sb.toString();
	}
	
}
