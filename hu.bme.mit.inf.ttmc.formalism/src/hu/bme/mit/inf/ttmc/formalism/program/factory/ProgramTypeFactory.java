package hu.bme.mit.inf.ttmc.formalism.program.factory;

import java.util.List;

import hu.bme.mit.inf.ttmc.core.factory.TypeFactory;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.type.ProcType;

public interface ProgramTypeFactory extends TypeFactory {

	public <R extends Type> ProcType<R> Proc(final List<? extends Type> paramTypes, final R returnType);

}
