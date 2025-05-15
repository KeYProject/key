/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.io.intermediate;

import de.uka.ilkd.key.logic.PosInTerm;

import org.key_project.logic.Name;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.Pair;

import org.jspecify.annotations.Nullable;

/**
 * Encapsulates intermediate information for constructing a built-in rule application.
 *
 * @author Dominic Scheurer
 */
public class BuiltInAppIntermediate extends AppIntermediate {

    private final String ruleName;
    private final Pair<Integer, PosInTerm> posInfo;
    private final @Nullable String contract;
    private final @Nullable String modality;
    private final @Nullable ImmutableList<Pair<Integer, PosInTerm>> builtInIfInsts;
    private final @Nullable ImmutableList<Name> newNames;

    public BuiltInAppIntermediate(
            String ruleName,
            Pair<Integer, PosInTerm> pos,
            @Nullable String contract,
            @Nullable String modality,
            @Nullable ImmutableList<Pair<Integer, PosInTerm>> builtInIfInsts,
            @Nullable ImmutableList<Name> newNames) {
        this.ruleName = ruleName;
        this.posInfo = pos;
        this.contract = contract;
        this.modality = modality;
        this.builtInIfInsts = builtInIfInsts;
        this.newNames = newNames;
    }

    public @Nullable String getRuleName() {
        return ruleName;
    }

    public Pair<Integer, PosInTerm> getPosInfo() {
        return posInfo;
    }

    public @Nullable String getContract() {
        return contract;
    }

    public @Nullable String getModality() {
        return modality;
    }

    public @Nullable ImmutableList<Pair<Integer, PosInTerm>> getBuiltInIfInsts() {
        return builtInIfInsts;
    }

    /*
     * (non-Javadoc)
     *
     * @see de.uka.ilkd.key.proof.io.intermediate.AppIntermediate#getNewNames()
     */
    @Override
    public @Nullable ImmutableList<Name> getNewNames() {
        return newNames;
    }

}
