/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testgen;

import org.jspecify.annotations.Nullable;

/**
 * Reference expression.
 * <p>
 * Example: rcObj.field, where rcObjType is the type of rcObj. The prefix "rc" stands for
 * receiver.
 *
 * @author gladisch
 */
public record RefEx(@Nullable String rcObjType, String rcObj, String fieldType, String field) {
    @Override
    public String toString() {
        if (rcObjType != null && !rcObjType.isEmpty()) {
            return "((" + rcObjType + ")" + rcObj + ")." + field;
        }
        return rcObj + "." + field;
    }
}
