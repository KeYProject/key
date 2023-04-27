package de.uka.ilkd.key.java.transformations;


/**
 * @author Alexander Weigl
 * @version 1 (11/2/21)
 */
public class EvaluationException extends Exception {
    public EvaluationException(String message, Exception exception) {
        super(message, exception);
    }
}
