package org.key_project.extsourceview.transformer;

/**
 * Transformation failed because the sequent cant be transformed
 */
public class TransformException extends Exception {
    public TransformException(String message) {
        super(message);
    }

    public TransformException(String message, Exception cause) {
        super(message, cause);
    }
}
