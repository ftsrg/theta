package hu.bme.mit.theta.frontend.c.parser;

public class ParserException extends RuntimeException {

	/**
	 *
	 */
	private static final long serialVersionUID = 1L;

	public ParserException(String message, Exception cause) {
		super(message, cause);
	}

	public ParserException(String message) {
		super(message);
	}

}
