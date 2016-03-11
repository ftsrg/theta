package hu.bme.mit.inf.ttmc.constraint.decl.defaults;

import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.decl.defaults.AbstractDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.ParamRefExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.ParamRefExprImpl;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public abstract class AbstractParamDecl<DeclType extends Type> extends AbstractDecl<DeclType> implements ParamDecl<DeclType> {
	
	protected volatile ParamRefExpr<DeclType> ref;
	
	public AbstractParamDecl(final String name, final DeclType type) {
		super(name, type);
	}
	
	@Override
	public ParamRefExpr<DeclType> getRef() {
		if (ref == null) {
			ref = new ParamRefExprImpl<>(this);
		}
		
		return ref;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Param(");
		sb.append(getName());
		sb.append(" : ");
		sb.append(getType());
		sb.append(")");
		return sb.toString();
	}
	
}
