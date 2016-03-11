package hu.bme.mit.inf.ttmc.aiger;

import java.io.IOException;

import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;

public interface AIGERLoader {
	public STS load(String fileName, STSManager manager) throws IOException;
}
