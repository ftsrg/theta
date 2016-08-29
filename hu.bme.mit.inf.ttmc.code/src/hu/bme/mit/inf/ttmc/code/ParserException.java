package hu.bme.mit.inf.ttmc.code;

public class ParserException extends RuntimeException {

    public ParserException(String message, Exception cause) {
        super(message, cause);
    }
    
    public ParserException(String message) {
        super(message);
    }
	
}
