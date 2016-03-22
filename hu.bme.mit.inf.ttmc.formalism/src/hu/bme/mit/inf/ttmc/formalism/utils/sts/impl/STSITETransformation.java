package hu.bme.mit.inf.ttmc.formalism.utils.sts.impl;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.sts.impl.STSImpl;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.FormalismUtils;
import hu.bme.mit.inf.ttmc.formalism.utils.sts.STSTransformation;

public final class STSITETransformation implements STSTransformation {

	@Override
	public STS transform(final STS system) {
		final STSImpl.Builder builder = new STSImpl.Builder(system.getManager());
		for (final Expr<? extends BoolType> expr : system.getInit())
			builder.addInit(FormalismUtils.eliminate(expr, system.getManager()));
		for (final Expr<? extends BoolType> expr : system.getInvar())
			builder.addInvar(FormalismUtils.eliminate(expr, system.getManager()));
		for (final Expr<? extends BoolType> expr : system.getTrans())
			builder.addTrans(FormalismUtils.eliminate(expr, system.getManager()));
		builder.setProp(FormalismUtils.eliminate(system.getProp(), system.getManager()));

		return builder.build();
	}

}
