package hu.bme.mit.inf.ttmc.formalism.common.type.visitor;

import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.TypeVisitor;
import hu.bme.mit.inf.ttmc.formalism.common.type.ProcType;

public interface ProcTypeVisitor<P, R> extends TypeVisitor<P, R> {
	public <ReturnType extends Type> R visit(ProcType<ReturnType> type, P param);
}
