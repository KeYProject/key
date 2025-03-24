/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.data;

import de.uka.ilkd.key.macros.scripts.ProofScriptCommand;

/**
 * @author Alexander Weigl
 * @version 1 (29.10.23)
 */
public record ProofScriptCommandDesc(String macroId, String documentation) implements KeYDataTransferObject {
    public static ProofScriptCommandDesc from(ProofScriptCommand<?> proofScriptCommand) {
        return new ProofScriptCommandDesc(proofScriptCommand.getName(), proofScriptCommand.getDocumentation());
    }
}
