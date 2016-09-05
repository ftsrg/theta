package hu.bme.mit.inf.theta.formalism.common.type.visitor;

import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.core.utils.TypeVisitor;
import hu.bme.mit.inf.theta.formalism.common.type.ProcType;

public interface ProcTypeVisitor<P, R> extends TypeVisitor<P, R> {
	public <ReturnType extends Type> R visit(ProcType<ReturnType> type, P param);
}
