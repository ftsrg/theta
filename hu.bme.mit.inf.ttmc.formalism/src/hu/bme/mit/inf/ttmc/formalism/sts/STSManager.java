package hu.bme.mit.inf.ttmc.formalism.sts;

import hu.bme.mit.inf.ttmc.formalism.FormalismManager;
import hu.bme.mit.inf.ttmc.formalism.common.factory.VarDeclFactory;
import hu.bme.mit.inf.ttmc.formalism.sts.factory.STSExprFactory;

public interface STSManager extends FormalismManager {

	@Override
	public VarDeclFactory getDeclFactory();

	@Override
	public STSExprFactory getExprFactory();

}
