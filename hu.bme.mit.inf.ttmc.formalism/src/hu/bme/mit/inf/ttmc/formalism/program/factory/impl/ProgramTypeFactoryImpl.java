package hu.bme.mit.inf.ttmc.formalism.program.factory.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;

import hu.bme.mit.inf.ttmc.core.factory.TypeFactory;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.factory.impl.TypeFactoryDecorator;
import hu.bme.mit.inf.ttmc.formalism.common.type.ProcType;
import hu.bme.mit.inf.ttmc.formalism.common.type.impl.ProcTypeImpl;
import hu.bme.mit.inf.ttmc.formalism.program.factory.ProgramTypeFactory;

public class ProgramTypeFactoryImpl extends TypeFactoryDecorator implements ProgramTypeFactory {

	public ProgramTypeFactoryImpl(final TypeFactory factory) {
		super(factory);
	}

	@Override
	public <R extends Type> ProcType<R> Proc(final List<? extends Type> paramTypes, final R returnType) {
		checkNotNull(paramTypes);
		checkNotNull(returnType);
		return new ProcTypeImpl<>(paramTypes, returnType);
	}

}
