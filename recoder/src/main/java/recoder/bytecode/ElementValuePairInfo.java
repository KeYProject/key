/*
 * Created on 10.06.2005
 *
 * This file is part of the RECODER library and protected by the LGPL.
 *
 */
package recoder.bytecode;

import recoder.abstraction.ElementValuePair;

/**
 * @author Tobias Gutzmann
 */
public class ElementValuePairInfo implements ElementValuePair {
    private final String elementName;
    private final Object value;
    private final String parent;

    public ElementValuePairInfo(String elementName, Object value, String parent) {
        this.elementName = elementName;
        this.value = value;
        this.parent = parent;
    }

    public Object getValue() {
        return value;
    }

    public String getElementName() {
        return elementName;
    }

    public String getFullNameOfContainingAnnotation() {
        return parent;
    }

    public String toString() {
        return getElementName() + "=" + getValue();
    }
}
