package org.key_project.util.lookup;

/**
 * @author Alexander Weigl
 * @version 1 (13.01.19)
 */
public class InjectionException extends RuntimeException {
    private static final long serialVersionUID = 119998955722036861L;

    public InjectionException() {
        super();
    }

    public InjectionException(String message) {
        super(message);
    }

    public InjectionException(String message, Throwable cause) {
        super(message, cause);
    }

    public InjectionException(Throwable cause) {
        super(cause);
    }

    protected InjectionException(String message, Throwable cause, boolean enableSuppression,
            boolean writableStackTrace) {
        super(message, cause, enableSuppression, writableStackTrace);
    }
}
