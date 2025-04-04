/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.data;

import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;

/**
 * @author Alexander Weigl
 * @version 1 (13.10.23)
 */
public record MacroStatistic(KeyIdentifications.ProofId proofId, String macroId, int appliedRules,
                             int closedGoals) implements KeYDataTransferObject {
    public static MacroStatistic from(KeyIdentifications.ProofId proofId, ProofMacroFinishedInfo info) {
        return new MacroStatistic(proofId, info.getMacro().getName(), info.getAppliedRules(), info.getClosedGoals());
    }
}
