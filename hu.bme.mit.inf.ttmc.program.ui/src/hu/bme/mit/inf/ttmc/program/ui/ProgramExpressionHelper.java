package hu.bme.mit.inf.ttmc.program.ui;

import hu.bme.mit.inf.ttmc.constraint.ui.DeclarationHelper;
import hu.bme.mit.inf.ttmc.constraint.ui.ExpressionHelper;
import hu.bme.mit.inf.ttmc.formalism.program.factory.ProgramExprFactory;

public class ProgramExpressionHelper extends ExpressionHelper {

	public ProgramExpressionHelper(final ProgramExprFactory exprFactory, final DeclarationHelper declarationHelper) {
		super(exprFactory, declarationHelper);
	}

}
