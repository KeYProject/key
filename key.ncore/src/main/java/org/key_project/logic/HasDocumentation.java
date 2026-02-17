/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.logic;

import org.jspecify.annotations.Nullable;

public interface HasDocumentation {
    String getDocumentationKey();

    default @Nullable String getDocumentation() {
        return null;
    }

    record OptionCategory(String name) implements HasDocumentation {
        public String getDocumentationKey() {
            return "category/" + name;
        }
    }
}
