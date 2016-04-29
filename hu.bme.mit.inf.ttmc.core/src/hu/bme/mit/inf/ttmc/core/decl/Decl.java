package hu.bme.mit.inf.ttmc.core.decl;

import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.utils.DeclVisitor;

public interface Decl<DeclType extends Type> {
	public String getName();

	public DeclType getType();

	public <P, R> R accept(DeclVisitor<? super P, ? extends R> visitor, P param);
}
