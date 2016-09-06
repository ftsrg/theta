package hu.bme.mit.inf.theta.formalism.common.type.visitor;

import hu.bme.mit.inf.theta.core.utils.TypeVisitor;
import hu.bme.mit.inf.theta.formalism.common.type.UnitType;

public interface UnitTypeVisitor<P, R> extends TypeVisitor<P, R> {

	public R visit(UnitType type, P param);

}
