/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.proof.io.intermediate;

import org.key_project.logic.Name;
import org.key_project.logic.PosInTerm;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.Pair;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Encapsulates intermediate information for constructing a built-in rule application.
 *
 * @author Dominic Scheurer
 */
@NullMarked
public class BuiltInAppIntermediate extends AppIntermediate {

    private String ruleName;
    private Pair<Integer, PosInTerm> posInfo;
    private @Nullable String contract = null;
    private @Nullable String modality = null;
    private @Nullable ImmutableList<Pair<Integer, PosInTerm>> builtInIfInsts = null;
    private @Nullable ImmutableList<Name> newNames = null;

    public BuiltInAppIntermediate(String ruleName, Pair<Integer, PosInTerm> pos,
            @Nullable String contract, @Nullable String modality,
            @Nullable ImmutableList<Pair<Integer, PosInTerm>> builtInIfInsts,
            @Nullable ImmutableList<Name> newNames) {
        this.ruleName = ruleName;
        this.posInfo = pos;
        this.contract = contract;
        this.modality = modality;
        this.builtInIfInsts = builtInIfInsts;
        this.newNames = newNames;
    }

    @Override
    public String getRuleName() {
        return ruleName;
    }

    public Pair<Integer, PosInTerm> getPosInfo() {
        return posInfo;
    }

    public @Nullable String getContract() {
        return contract;
    }

    public @Nullable String getModality() { return modality; }

    public @Nullable ImmutableList<Pair<Integer, PosInTerm>> getBuiltInIfInsts() {
        return builtInIfInsts;
    }

    /*
     * (non-Javadoc)
     *
     * @see de.uka.ilkd.key.proof.io.intermediate.AppIntermediate#getNewNames()
     * The overridden declaration requires a non-null return type, but this implementation may
     * legitimately return {@code null}; the difference is suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:override.return.invalid")
    @Override
    public @Nullable ImmutableList<Name> getNewNames() {
        return newNames;
    }

}
