package hu.bme.mit.inf.ttmc.constraint.decl.defaults;

import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.ParamRefExpr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public abstract class AbstractParamDecl<DeclType extends Type> extends AbstractDecl<DeclType>
		implements ParamDecl<DeclType> {

	public AbstractParamDecl(final String name, final DeclType type) {
		super(name, type);
	}

	@Override
	public ParamRefExpr<DeclType> getRef() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
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
