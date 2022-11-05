// This file is part of the RECODER library and protected by the LGPL.

package recoder.bytecode;

import recoder.ParserException;

/**
 * Byte Code format Exception.
 *
 * @author AL
 */
public class ByteCodeFormatException extends ParserException {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -6748189319137209773L;

    /**
     * Trivial Constructor.
     */
    public ByteCodeFormatException() {
        super();
    }

    /**
     * Constructor with description text.
     *
     * @param msg a description.
     */
    public ByteCodeFormatException(String msg) {
        super(msg);
    }
}
