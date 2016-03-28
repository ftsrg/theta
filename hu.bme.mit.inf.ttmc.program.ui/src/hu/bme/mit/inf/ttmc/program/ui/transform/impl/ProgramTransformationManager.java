package hu.bme.mit.inf.ttmc.program.ui.transform.impl;

import hu.bme.mit.inf.ttmc.constraint.ui.transform.DeclTransformator;
import hu.bme.mit.inf.ttmc.constraint.ui.transform.ExprTransformator;
import hu.bme.mit.inf.ttmc.constraint.ui.transform.TransformationManager;
import hu.bme.mit.inf.ttmc.constraint.ui.transform.TypeTransformator;
import hu.bme.mit.inf.ttmc.formalism.program.ProgramManager;
import hu.bme.mit.inf.ttmc.program.ui.transform.StmtTransformator;

public class ProgramTransformationManager implements TransformationManager {

	private final ProgramTypeTransformator typeTransformator;
	private final ProgramDeclTransformator declTransformator;
	private final ProgramExprTransformator exprTransformator;
	private final ProgramStmtTransformator stmtTransformator;

	public ProgramTransformationManager(final ProgramManager manager) {
		typeTransformator = new ProgramTypeTransformator(this, manager.getTypeFactory());
		declTransformator = new ProgramDeclTransformator(this, manager.getDeclFactory());
		exprTransformator = new ProgramExprTransformator(this, manager.getExprFactory());
		stmtTransformator = new ProgramStmtTransformator(this, manager.getStmtFactory());
	}

	@Override
	public TypeTransformator getTypeTransformator() {
		return typeTransformator;
	}

	@Override
	public DeclTransformator getDeclTransformator() {
		return declTransformator;
	}

	@Override
	public ExprTransformator getExprTransformator() {
		return exprTransformator;
	}

	public StmtTransformator getStmtTransformator() {
		return stmtTransformator;
	}

}
