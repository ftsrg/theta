package hu.bme.mit.inf.ttmc.code;

public class TransformException extends RuntimeException {

    public TransformException(String message, Exception cause) {
        super(message, cause);
    }
    
    public TransformException(String message) {
        super(message);
    }
	
}
