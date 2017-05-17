package hu.bme.mit.theta.formalism.sts.utils;

import hu.bme.mit.theta.formalism.sts.STS;

/**
 * Common interface for transforming STSs.
 */
public interface STSTransformation {
	/**
	 * Apply the transformation.
	 *
	 * @param system Input STS
	 * @return Transformed STS
	 */
	STS transform(STS system);
}
