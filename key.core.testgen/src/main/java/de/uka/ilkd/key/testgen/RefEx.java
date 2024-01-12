/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testgen;

/**
 * Reference expression
 *
 * @author gladisch
 */
public class RefEx {
    public final String rcObjType;
    public final String rcObj;
    public final String fieldType;
    public final String field;

    /**
     * Example: rcObj.field, where rcObjType is the type of rcObj. The prefix "rc" stands for
     * receiver.
     */
    public RefEx(String rcObjType, String rcObj, String fieldType, String field) {
        this.rcObjType = rcObjType;
        this.rcObj = rcObj;
        this.fieldType = fieldType;
        this.field = field;
    }

    @Override
    public String toString() {
        if (rcObjType != null && !rcObjType.isEmpty()) {
            return "((" + rcObjType + ")" + rcObj + ")." + field;
        }
        return rcObj + "." + field;
    }
}
