/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.remoteapi;

import de.uka.ilkd.key.macros.ProofMacro;

public record MacroDescription(String name, String description, String category) {
    public static MacroDescription from(ProofMacro m) {
        return new MacroDescription(m.getName(), m.getDescription(), m.getCategory());
    }
}
