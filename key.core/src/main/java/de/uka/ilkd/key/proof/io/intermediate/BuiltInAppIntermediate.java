/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.io.intermediate;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.util.Pair;

import org.key_project.util.collection.ImmutableList;

/**
 * Encapsulates intermediate information for constructing a built-in rule application.
 *
 * @author Dominic Scheurer
 */
public class BuiltInAppIntermediate extends AppIntermediate {

    private String ruleName = null;
    private Pair<Integer, PosInTerm> posInfo = null;
    private String contract = null;
    private String modality = null;
    private ImmutableList<Pair<Integer, PosInTerm>> builtInIfInsts = null;
    private ImmutableList<Name> newNames = null;

    public BuiltInAppIntermediate(String ruleName, Pair<Integer, PosInTerm> pos, String contract,
            String modality, ImmutableList<Pair<Integer, PosInTerm>> builtInIfInsts,
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

    public Pair<Integer, PosInTerm> getPosInfo() {
        return posInfo;
    }

    public String getContract() {
        return contract;
    }

    public String getModality() { return modality; }

    public ImmutableList<Pair<Integer, PosInTerm>> getBuiltInIfInsts() {
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

}
