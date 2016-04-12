package hu.bme.mit.inf.ttmc.formalism.program.impl;

import hu.bme.mit.inf.ttmc.core.ConstraintManager;
import hu.bme.mit.inf.ttmc.formalism.common.factory.StmtFactory;
import hu.bme.mit.inf.ttmc.formalism.common.factory.impl.StmtFactoryImpl;
import hu.bme.mit.inf.ttmc.formalism.program.ProgramManager;
import hu.bme.mit.inf.ttmc.formalism.program.factory.ProgramDeclFactory;
import hu.bme.mit.inf.ttmc.formalism.program.factory.ProgramExprFactory;
import hu.bme.mit.inf.ttmc.formalism.program.factory.ProgramTypeFactory;
import hu.bme.mit.inf.ttmc.formalism.program.factory.impl.ProgramDeclFactoryImpl;
import hu.bme.mit.inf.ttmc.formalism.program.factory.impl.ProgramExprFactoryImpl;
import hu.bme.mit.inf.ttmc.formalism.program.factory.impl.ProgramTypeFactoryImpl;

public class ProgramManagerImpl implements ProgramManager {

	private final ProgramTypeFactory typeFactory;
	private final ProgramDeclFactory declFactory;
	private final ProgramExprFactory exprFactory;
	private final StmtFactory stmtFactory;

	public ProgramManagerImpl(final ConstraintManager manager) {
		typeFactory = new ProgramTypeFactoryImpl(manager.getTypeFactory());
		declFactory = new ProgramDeclFactoryImpl(manager.getDeclFactory());
		exprFactory = new ProgramExprFactoryImpl(manager.getExprFactory());
		stmtFactory = new StmtFactoryImpl();
	}

	@Override
	public ProgramTypeFactory getTypeFactory() {
		return typeFactory;
	}

	@Override
	public ProgramDeclFactory getDeclFactory() {
		return declFactory;
	}

	@Override
	public ProgramExprFactory getExprFactory() {
		return exprFactory;
	}

	@Override
	public StmtFactory getStmtFactory() {
		return stmtFactory;
	}

}
