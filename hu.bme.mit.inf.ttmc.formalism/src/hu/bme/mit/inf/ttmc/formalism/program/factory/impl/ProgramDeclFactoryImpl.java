package hu.bme.mit.inf.ttmc.formalism.program.factory.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.HashMap;
import java.util.List;

import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.factory.DeclFactory;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ProcDecl;
import hu.bme.mit.inf.ttmc.formalism.common.decl.impl.ProcDeclImpl;
import hu.bme.mit.inf.ttmc.formalism.common.factory.impl.VarDeclFactoryImpl;
import hu.bme.mit.inf.ttmc.formalism.program.factory.ProgramDeclFactory;

public class ProgramDeclFactoryImpl extends VarDeclFactoryImpl implements ProgramDeclFactory {

	private final HashMap<String, ProcDecl<?>> nameToProc;

	public ProgramDeclFactoryImpl(final DeclFactory factory) {
		super(factory);
		nameToProc = new HashMap<>();
	}

	@Override
	public <R extends Type> ProcDecl<R> Proc(final String name,
			final List<? extends ParamDecl<? extends Type>> paramDecls, final R returnType) {
		checkNotNull(name);
		checkNotNull(paramDecls);
		checkNotNull(returnType);
		checkArgument(name.length() > 0);
		checkArgument(nameToProc.get(name) == null);

		final ProcDecl<R> procDecl = new ProcDeclImpl<>(name, paramDecls, returnType);
		nameToProc.put(name, procDecl);
		return procDecl;
	}

}
