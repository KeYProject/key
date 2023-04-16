// This file is part of the RECODER library and protected by the LGPL

package recoder.kit;

import recoder.NamedModelElement;

/**
 * Problem report indicating that the planned transformation produces a name conflict with an
 * existing model element.
 */
public class NameConflict extends Conflict {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -2147929685769271562L;
    private final NamedModelElement reason;

    /**
     * Creates a new problem report with the given element as the reason of the conflict.
     */
    public NameConflict(NamedModelElement reason) {
        this.reason = reason;
    }

    /**
     * Returns the element that produced the name conflict.
     *
     * @return a named element.
     */
    public NamedModelElement getReason() {
        return reason;
    }
}
