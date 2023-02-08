/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
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
