// This file is part of the RECODER library and protected by the LGPL.

package recoder.kit;

import recoder.abstraction.Method;

/**
 * Problem report indicating that a static method has been overwritten with a non-static version.
 */
public class NonStaticOverwrite extends Conflict {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -3618890938924075301L;
    private final Method method;

    public NonStaticOverwrite(Method method) {
        this.method = method;
    }

    public Method getMethod() {
        return method;
    }
}
