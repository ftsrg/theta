package hu.bme.mit.inf.ttmc.core.factory;

import hu.bme.mit.inf.ttmc.core.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.core.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.core.type.Type;

public interface DeclFactory {
	
	public <T extends Type> ConstDecl<T> Const(final String name, final T type);
		
	public <T extends Type> ParamDecl<T> Param(final String name, final T type);
	
}
