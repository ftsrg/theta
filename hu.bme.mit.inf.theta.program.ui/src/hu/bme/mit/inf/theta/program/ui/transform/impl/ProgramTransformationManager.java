package hu.bme.mit.inf.theta.program.ui.transform.impl;

import hu.bme.mit.inf.theta.constraint.ui.transform.DeclTransformator;
import hu.bme.mit.inf.theta.constraint.ui.transform.ExprTransformator;
import hu.bme.mit.inf.theta.constraint.ui.transform.TransformationManager;
import hu.bme.mit.inf.theta.constraint.ui.transform.TypeTransformator;
import hu.bme.mit.inf.theta.program.ui.transform.StmtTransformator;
import hu.bme.mit.inf.theta.program.ui.transform.impl.ProgramDeclTransformator;
import hu.bme.mit.inf.theta.program.ui.transform.impl.ProgramExprTransformator;
import hu.bme.mit.inf.theta.program.ui.transform.impl.ProgramStmtTransformator;
import hu.bme.mit.inf.theta.program.ui.transform.impl.ProgramTypeTransformator;

public class ProgramTransformationManager implements TransformationManager {

	private final ProgramTypeTransformator typeTransformator;
	private final ProgramDeclTransformator declTransformator;
	private final ProgramExprTransformator exprTransformator;
	private final ProgramStmtTransformator stmtTransformator;

	public ProgramTransformationManager() {
		typeTransformator = new ProgramTypeTransformator(this);
		declTransformator = new ProgramDeclTransformator(this);
		exprTransformator = new ProgramExprTransformator(this);
		stmtTransformator = new ProgramStmtTransformator(this);
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
