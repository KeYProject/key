/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.data;

import de.uka.ilkd.key.macros.ProofMacro;

/**
 *
 * @param name
 * @param description
 * @param category
 */
public record MacroDescription(String name, String description, String category)
        implements KeYDataTransferObject {
    public static MacroDescription from(ProofMacro m) {
        return new MacroDescription(m.getName(), m.getDescription(), m.getCategory());
    }
}
