package hu.bme.mit.inf.ttmc.cegar.common;

import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;

public interface ICEGARBuilder {
	ICEGARLoop build();

	ICEGARBuilder manager(final STSManager manager);
}
