package comment;

public class InsufficientRightsException extends Exception {

	public InsufficientRightsException() {
		super();
	}

	public InsufficientRightsException(String arg0) {
		super(arg0);
	}

	public InsufficientRightsException(String arg0, Throwable arg1) {
		super(arg0, arg1);
	}

	public InsufficientRightsException(Throwable arg0) {
		super(arg0);
	}
}
