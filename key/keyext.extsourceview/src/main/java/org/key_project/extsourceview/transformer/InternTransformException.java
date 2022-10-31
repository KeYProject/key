package org.key_project.extsourceview.transformer;

/**
 * Transformation failed due to some unforseen internal error
 */
public class InternTransformException extends Exception {
    public InternTransformException(String message) {
        super(message);
    }

    public InternTransformException(String message, Exception cause) {
        super(message, cause);
    }
}
