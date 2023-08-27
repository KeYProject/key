/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.bytecode;

import java.util.List;

import recoder.abstraction.AnnotationUse;
import recoder.abstraction.ElementValuePair;

/**
 * @author gutzmann
 */
public class AnnotationUseInfo implements AnnotationUse {
    protected final List<ElementValuePair> elementValuePairs;

    protected final String fullAnnotationTypeName;

    /**
     * @param accessFlags
     * @param name
     */
    public AnnotationUseInfo(String fullName, List<ElementValuePair> evpl) {
        super();
        this.elementValuePairs = evpl;
        this.fullAnnotationTypeName = fullName;
    }

    public List<ElementValuePair> getElementValuePairs() {
        return elementValuePairs;
    }

    private String getParamStr() {
        StringBuilder res = new StringBuilder();
        boolean first = true;
        for (ElementValuePair evp : elementValuePairs) {
            if (!first) {
                res.append(",");
            }
            first = false;
            res.append(evp.toString());
        }
        return res.toString();
    }

    public String toString() {
        return "@" + getFullReferencedName() + "(" + getParamStr() + ")";
    }

    public String getFullReferencedName() {
        return fullAnnotationTypeName;
    }

    public String getReferencedName() {
        return fullAnnotationTypeName.substring(fullAnnotationTypeName.lastIndexOf('.') + 1);
    }
}
