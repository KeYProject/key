/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.io.intermediate;

import de.uka.ilkd.key.logic.PosInTerm;

import org.key_project.logic.Name;
import org.key_project.util.collection.ImmutableList;

/**
 * Encapsulates intermediate information for constructing a built-in rule application.
 *
 * @author Dominic Scheurer
 */
public class BuiltInAppIntermediate extends AppIntermediate {

    private String ruleName;
    private PosInfo posInfo;
    private String contract;
    private String modality;
    private ImmutableList<PosInfo> builtInIfInsts;
    private ImmutableList<Name> newNames;

    public BuiltInAppIntermediate(String ruleName, PosInfo pos, String contract,
            String modality, ImmutableList<PosInfo> builtInIfInsts,
            ImmutableList<Name> newNames) {
        this.ruleName = ruleName;
        this.posInfo = pos;
        this.contract = contract;
        this.modality = modality;
        this.builtInIfInsts = builtInIfInsts;
        this.newNames = newNames;
    }

    public String getRuleName() {
        return ruleName;
    }

    public PosInfo getPosInfo() {
        return posInfo;
    }

    public String getContract() {
        return contract;
    }

    public String getModality() { return modality; }

    public ImmutableList<PosInfo> getBuiltInIfInsts() {
        return builtInIfInsts;
    }

    /*
     * (non-Javadoc)
     *
     * @see de.uka.ilkd.key.proof.io.intermediate.AppIntermediate#getNewNames()
     */
    @Override
    public ImmutableList<Name> getNewNames() {
        return newNames;
    }

    public record PosInfo(Integer first, PosInTerm second) {
    }
}
