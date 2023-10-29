package org.keyproject.key.api.data;

import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;

/**
 * @author Alexander Weigl
 * @version 1 (13.10.23)
 */
public record MacroStatistic(KeyIdentifications.ProofId proofId, String macroId, boolean cancelled, int appliedRules,
                             int closedGoals) {
    public static MacroStatistic from(KeyIdentifications.ProofId proofId, ProofMacroFinishedInfo info) {
        return new MacroStatistic(proofId, info.getMacro().getName(), info.isCancelled(),
                info.getAppliedRules(), info.getClosedGoals());
    }
}
