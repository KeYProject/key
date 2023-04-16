// This file is part of the RECODER library and protected by the LGPL.

package recoder;

/**
 * Model exception.
 *
 * @author <TT>AutoDoc</TT>
 */
public class ModelException extends RuntimeException {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -2334025270847777367L;

    /**
     * Model exception.
     */
    public ModelException() {
        super();
    }

    /**
     * Model exception.
     *
     * @param s a string.
     */
    public ModelException(String s) {
        super(s);
    }
}
