package hu.bme.mit.inf.theta.constraint.ui.transform;

import hu.bme.mit.inf.theta.constraint.model.Declaration;
import hu.bme.mit.inf.theta.core.decl.Decl;
import hu.bme.mit.inf.theta.core.type.Type;

public interface DeclTransformator {

	public Decl<? extends Type, ?> transform(Declaration declaration);

}
