package hu.bme.mit.inf.theta.program.ui;

import java.util.Collection;

import hu.bme.mit.inf.theta.constraint.ui.ConstraintModel;
import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.formalism.common.decl.ProcDecl;

public interface ProgramModel extends ConstraintModel {

	public Collection<ProcDecl<? extends Type>> getProcDecls();

}