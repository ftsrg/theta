package hu.bme.mit.inf.ttmc.constraint.factory;

import hu.bme.mit.inf.ttmc.constraint.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public interface DeclFactory {
	
	public <T extends Type> ConstDecl<T> Const(final String name, final T type);
		
	public <T extends Type> ParamDecl<T> Param(final String name, final T type);
	
}
