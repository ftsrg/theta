package hu.bme.mit.theta.formalism.sts.aiger;

import java.io.IOException;

import hu.bme.mit.theta.formalism.sts.STS;

/**
 * Interface for parsing hardware circuits described in the AIGER format.
 */
public interface AigerParser {
	/**
	 * Parse a hardware circuit in AIGER format to a STS.
	 *
	 * @param fileName Path and name of the aiger file
	 * @return STS representation of the circuit
	 * @throws IOException
	 */
	STS parse(String fileName) throws IOException;
}
