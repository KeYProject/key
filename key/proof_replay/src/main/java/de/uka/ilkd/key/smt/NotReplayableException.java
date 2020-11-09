package de.uka.ilkd.key.smt;

public class NotReplayableException extends RuntimeException {
    public NotReplayableException(String message) {
        super(message);
    }

    public NotReplayableException(String message, Throwable cause) {
        super(message, cause);
    }
}
