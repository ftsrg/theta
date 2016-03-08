package hu.bme.mit.inf.ttmc.formalism.utils.sts;

import hu.bme.mit.inf.ttmc.formalism.sts.STS;

/**
 * Common interface for transformations on STSs.
 * @author Akos Hajdu
 */
public interface STSTransformation {
	/**
	 * Transform an STS.
	 * @param system Input STS
	 * @return Transformed STS
	 */
	public STS transform(STS system);
}
