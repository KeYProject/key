// This file is part of the RECODER library and protected by the LGPL

package recoder.kit;

/**
 * this class implements basic functions for type handling.
 *
 * @author Dirk Heuzeroth
 */

public class NameClashException extends Exception {
    /**
     * serialization id
     */
    private static final long serialVersionUID = -8660164254613770539L;

    NameClashException() {
        super();
    }

    NameClashException(String msg) {
        super(msg);
    }
}
