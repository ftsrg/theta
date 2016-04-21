package hu.bme.mit.inf.ttmc.formalism.common.type.visitor;

import hu.bme.mit.inf.ttmc.core.utils.TypeVisitor;
import hu.bme.mit.inf.ttmc.formalism.common.type.UnitType;

public interface UnitTypeVisitor<P, R> extends TypeVisitor<P, R> {

	public R visit(UnitType type, P param);

}
