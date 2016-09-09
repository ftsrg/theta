package hu.bme.mit.inf.theta.aiger;

import java.io.IOException;

import hu.bme.mit.inf.theta.formalism.sts.STS;

public interface AIGERLoader {
	public STS load(String fileName) throws IOException;
}
