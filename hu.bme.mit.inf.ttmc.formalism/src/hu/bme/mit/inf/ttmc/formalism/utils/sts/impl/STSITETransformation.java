package hu.bme.mit.inf.ttmc.formalism.utils.sts.impl;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.sts.impl.STSImpl;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.FormalismUtils;
import hu.bme.mit.inf.ttmc.formalism.utils.sts.STSTransformation;

public final class STSITETransformation implements STSTransformation {
	ConstraintManager manager;
	
	public STSITETransformation(ConstraintManager manager) {
		this.manager = manager;
	}
	
	@Override
	public STS transform(STS system) {
		STSImpl.Builder builder = new STSImpl.Builder();
		for (Expr<? extends BoolType> expr : system.getInit()) builder.addInit(FormalismUtils.eliminate(expr, manager));
		for (Expr<? extends BoolType> expr : system.getInvar()) builder.addInvar(FormalismUtils.eliminate(expr, manager));
		for (Expr<? extends BoolType> expr : system.getTrans()) builder.addTrans(FormalismUtils.eliminate(expr, manager));
		builder.setProp(FormalismUtils.eliminate(system.getProp(), manager));

		return builder.build();
	}

}
