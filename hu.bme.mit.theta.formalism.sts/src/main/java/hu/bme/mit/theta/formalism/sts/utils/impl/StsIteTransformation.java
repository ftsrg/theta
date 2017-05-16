package hu.bme.mit.theta.formalism.sts.utils.impl;

import hu.bme.mit.theta.core.utils.impl.ExprUtils;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.formalism.sts.utils.STSTransformation;

/**
 * A transformation eliminating if-then-else expressions.
 */
public final class StsIteTransformation implements STSTransformation {

	@Override
	public STS transform(final STS system) {
		final STS.Builder builder = STS.builder();
		builder.addInit(ExprUtils.eliminateITE(system.getInit()));
		builder.addTrans(ExprUtils.eliminateITE(system.getTrans()));
		builder.setProp(ExprUtils.eliminateITE(system.getProp()));
		return builder.build();
	}

}
