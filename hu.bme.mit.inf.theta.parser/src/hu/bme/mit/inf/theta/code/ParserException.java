package hu.bme.mit.inf.theta.code;

public class ParserException extends RuntimeException {

    public ParserException(String message, Exception cause) {
        super(message, cause);
    }
    
    public ParserException(String message) {
        super(message);
    }
	
}
