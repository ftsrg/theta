package hu.bme.mit.inf.ttmc.constraint.decl.impl;

import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.decl.impl.AbstractDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.ParamRefExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.ParamRefExprImpl;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public class ParamDeclImpl<DeclType extends Type> extends AbstractDecl<DeclType> implements ParamDecl<DeclType> {
	
	protected volatile ParamRefExpr<DeclType> ref;
	
	public ParamDeclImpl(final String name, final DeclType type) {
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
