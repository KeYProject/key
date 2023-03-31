// This file is part of the RECODER library and protected by the LGPL.

package recoder.kit;

import recoder.abstraction.Method;

/**
 * Problem report indicating that a method has been overwritten with a version that offers more
 * strict exceptions.
 */
public class UncoveredExceptionsOverwrite extends Conflict {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 1648909642243255075L;
    private final Method method;

    public UncoveredExceptionsOverwrite(Method method) {
        this.method = method;
    }

    public Method getMethod() {
        return method;
    }
}
