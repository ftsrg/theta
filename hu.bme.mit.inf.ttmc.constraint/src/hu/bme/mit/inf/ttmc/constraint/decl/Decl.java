package hu.bme.mit.inf.ttmc.constraint.decl;

import hu.bme.mit.inf.ttmc.constraint.decl.Decl;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public interface Decl<DeclType extends Type> {
	public String getName();
	public DeclType getType();
}
