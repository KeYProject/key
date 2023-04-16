// This file is part of the RECODER library and protected by the LGPL.

package recoder.kit.pattern;

import recoder.ModelException;

public class InconsistentPatternException extends ModelException {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 1L;

    public InconsistentPatternException() {
        super();
    }

    public InconsistentPatternException(String s) {
        super(s);
    }
}
