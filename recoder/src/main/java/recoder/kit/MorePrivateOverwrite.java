// This file is part of the RECODER library and protected by the LGPL.

package recoder.kit;

import recoder.abstraction.Method;

/**
 * Problem report indicating that a method has been overwritten with a lower visibility.
 */
public class MorePrivateOverwrite extends Conflict {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 8547386567851667884L;
    private final Method method;

    public MorePrivateOverwrite(Method method) {
        this.method = method;
    }

    public Method getMethod() {
        return method;
    }
}
