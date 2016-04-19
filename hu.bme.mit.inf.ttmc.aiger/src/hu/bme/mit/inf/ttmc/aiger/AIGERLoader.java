package hu.bme.mit.inf.ttmc.aiger;

import java.io.IOException;

import hu.bme.mit.inf.ttmc.formalism.sts.STS;

public interface AIGERLoader {
	public STS load(String fileName) throws IOException;
}
