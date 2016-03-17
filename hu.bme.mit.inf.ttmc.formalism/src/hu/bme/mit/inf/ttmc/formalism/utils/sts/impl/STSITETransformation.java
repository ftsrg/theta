package hu.bme.mit.inf.ttmc.formalism.utils.sts.impl;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.sts.impl.STSImpl;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.FormalismExprITEEliminator;
import hu.bme.mit.inf.ttmc.formalism.utils.sts.STSTransformation;

public final class STSITETransformation implements STSTransformation {
	private final FormalismExprITEEliminator eliminator;
	
	public STSITETransformation(ConstraintManager manager) {
		eliminator = new FormalismExprITEEliminator(manager);
	}
	
	@Override
	public STS transform(STS system) {
		STSImpl.Builder builder = new STSImpl.Builder();
		for (Expr<? extends BoolType> expr : system.getInit()) builder.addInit(eliminator.eliminate(expr));
		for (Expr<? extends BoolType> expr : system.getInvar()) builder.addInvar(eliminator.eliminate(expr));
		for (Expr<? extends BoolType> expr : system.getTrans()) builder.addTrans(eliminator.eliminate(expr));
		builder.setProp(eliminator.eliminate(system.getProp()));

		return builder.build();
	}

}
