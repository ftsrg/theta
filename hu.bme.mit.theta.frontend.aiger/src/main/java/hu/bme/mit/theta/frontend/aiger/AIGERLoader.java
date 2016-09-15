package hu.bme.mit.theta.frontend.aiger;

import java.io.IOException;

import hu.bme.mit.theta.formalism.sts.STS;

public interface AIGERLoader {
	public STS load(String fileName) throws IOException;
}
