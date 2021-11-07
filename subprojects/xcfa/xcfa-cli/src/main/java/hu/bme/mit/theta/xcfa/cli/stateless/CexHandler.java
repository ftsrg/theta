package hu.bme.mit.theta.xcfa.cli.stateless;

public class CexHandler {
	enum OutputOptions {
		NONE, WITNESS_ONLY, OUTPUT_RESULTS;
	}

	CexHandler INSTANCE = new CexHandler();

	private OutputOptions outputConfiguration = OutputOptions.NONE;

	private CexHandler() {

	}

	public void setOutput(OutputOptions outputConfiguration) {
		this.outputConfiguration = outputConfiguration;
	}

}
