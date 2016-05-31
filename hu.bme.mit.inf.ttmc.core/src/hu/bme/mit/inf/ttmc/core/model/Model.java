
package hu.bme.mit.inf.ttmc.core.model;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.core.decl.ConstDecl;

public interface Model extends Assignment {

	@Override
	Collection<? extends ConstDecl<?>> getDecls();

}
