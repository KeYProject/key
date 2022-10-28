/** this exception is shown if an assertion has failed */
package de.uka.ilkd.key.util;

public class AssertionFailure extends RuntimeException {


    /**
     *
     */
    private static final long serialVersionUID = -235001842777133987L;

    public AssertionFailure() {
        super();
    }

    public AssertionFailure(String msg) {
        super(msg);
    }



}
