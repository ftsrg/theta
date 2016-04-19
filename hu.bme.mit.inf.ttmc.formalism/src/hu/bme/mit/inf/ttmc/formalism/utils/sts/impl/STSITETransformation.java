package hu.bme.mit.inf.ttmc.formalism.utils.sts.impl;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.sts.impl.STSImpl;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.FormalismUtils;
import hu.bme.mit.inf.ttmc.formalism.utils.sts.STSTransformation;

public final class STSITETransformation implements STSTransformation {

	@Override
	public STS transform(final STS system) {
		final STSImpl.Builder builder = new STSImpl.Builder();
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
