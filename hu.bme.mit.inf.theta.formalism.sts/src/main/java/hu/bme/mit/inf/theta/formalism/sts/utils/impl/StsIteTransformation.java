package hu.bme.mit.inf.theta.formalism.sts.utils.impl;

import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.type.BoolType;
import hu.bme.mit.inf.theta.formalism.sts.STS;
import hu.bme.mit.inf.theta.formalism.sts.impl.StsImpl;
import hu.bme.mit.inf.theta.formalism.sts.utils.STSTransformation;
import hu.bme.mit.inf.theta.formalism.utils.FormalismUtils;

public final class StsIteTransformation implements STSTransformation {

	@Override
	public STS transform(final STS system) {
		final StsImpl.Builder builder = new StsImpl.Builder();
		for (final Expr<? extends BoolType> expr : system.getInit())
			builder.addInit(FormalismUtils.eliminate(expr));
		for (final Expr<? extends BoolType> expr : system.getInvar())
			builder.addInvar(FormalismUtils.eliminate(expr));
		for (final Expr<? extends BoolType> expr : system.getTrans())
			builder.addTrans(FormalismUtils.eliminate(expr));
		builder.setProp(FormalismUtils.eliminate(system.getProp()));

		return builder.build();
	}

}
