package hu.bme.mit.inf.ttmc.program.ui.helpers;

import hu.bme.mit.inf.ttmc.constraint.ui.helpers.DeclarationHelper;
import hu.bme.mit.inf.ttmc.constraint.ui.helpers.ExpressionHelper;
import hu.bme.mit.inf.ttmc.formalism.program.factory.ProgramExprFactory;

public class ProgramExpressionHelper extends ExpressionHelper {

	public ProgramExpressionHelper(final ProgramExprFactory exprFactory, final DeclarationHelper declarationHelper) {
		super(exprFactory, declarationHelper);
	}

}
