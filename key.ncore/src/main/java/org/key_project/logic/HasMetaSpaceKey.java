/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.logic;

import org.jspecify.annotations.Nullable;

/// Mark items of the namespace which can have entries in the {@link
/// de.uka.ilkd.key.logic.MetaSpace}.
///
/// @author weigl
public interface HasMetaSpaceKey {
    String getMetaKey();

    default @Nullable String getDocumentation() {
        return null;
    }

    record OptionCategory(String name) implements HasMetaSpaceKey {
        public String getMetaKey() {
            return "category/" + name;
        }
    }
}
