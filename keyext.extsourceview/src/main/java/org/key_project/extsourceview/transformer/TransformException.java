package org.key_project.extsourceview.transformer;

/**
 * Transformation failed because the sequent cant be transformed
 */
public class TransformException extends Exception {

    public final String Extra;

    public TransformException(String message) {
        super(message);
        Extra = "";
    }

    public TransformException(String message, String extra) {
        super(message);
        Extra = extra;
    }

    public TransformException(String message, Exception cause) {
        super(message, cause);
        Extra = "";
    }

}

