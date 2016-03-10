package hu.bme.mit.inf.ttmc.formalism.common.decl.impl;

import hu.bme.mit.inf.ttmc.constraint.decl.impl.AbstractDecl;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.impl.VarRefExprImpl;

public class VarDeclImpl<DeclType extends Type> extends AbstractDecl<DeclType> implements VarDecl<DeclType> {

	protected volatile VarRefExpr<DeclType> ref;
	
	public VarDeclImpl(final String name, final DeclType type) {
		super(name, type);
	}
	
	@Override
	public VarRefExpr<DeclType> getRef() {
		if (ref == null) {
			ref = new VarRefExprImpl<>(this);
		}
		
		return ref;
	}
	
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Var(");
		sb.append(getName());
		sb.append(" : ");
		sb.append(getType().toString());
		sb.append(")");
		return sb.toString();
	}
	
}
