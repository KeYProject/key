// This file is part of the RECODER library and protected by the LGPL.

package recoder.kit;

import recoder.NamedModelElement;

/**
 * Problem report indicating that a chosen name is illegal, for instance a keyword.
 */
public class IllegalName extends Problem {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -6773990661739949555L;
    private final NamedModelElement element;

    public IllegalName(NamedModelElement element) {
        this.element = element;
    }

    public NamedModelElement getElement() {
        return element;
    }
}
