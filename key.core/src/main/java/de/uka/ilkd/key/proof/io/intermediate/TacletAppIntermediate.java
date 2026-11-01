/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.proof.io.intermediate;

import java.util.List;

import org.key_project.logic.Name;
import org.key_project.logic.PosInTerm;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.Pair;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Encapsulates intermediate information for constructing a taclet application.
 *
 * @author Dominic Scheurer
 */
@NullMarked
public class TacletAppIntermediate extends AppIntermediate {

    private String tacletName;
    private Pair<Integer, PosInTerm> posInfo;
    private @Nullable List<String> insts = null;
    private ImmutableList<String> ifSeqFormulaList;
    private ImmutableList<String> ifDirectFormulaList;
    private @Nullable ImmutableList<Name> newNames = null;

    /**
     * Constructs a new intermediate taclet application.
     *
     * @param tacletName Name of the taclet.
     * @param posInfo Position information (Integer representing position of the target formula,
     *        PosInTerm for relevant term inside the formula).
     * @param insts Schema variable instantiations.
     * @param ifSeqFormulaList
     * @param ifDirectFormulaList
     * @param newNames New names registered during taclet application.
     */
    public TacletAppIntermediate(String tacletName, Pair<Integer, PosInTerm> posInfo,
            @Nullable List<String> insts, ImmutableList<String> ifSeqFormulaList,
            ImmutableList<String> ifDirectFormulaList, @Nullable ImmutableList<Name> newNames) {
        // Taclet names are internalized later, so we don't waste memory
        this.tacletName = tacletName.intern();
        this.posInfo = posInfo;
        this.insts = insts;
        this.ifSeqFormulaList = ifSeqFormulaList;
        this.ifDirectFormulaList = ifDirectFormulaList;
        this.newNames = newNames;
    }

    @Override
    public String getRuleName() {
        return tacletName;
    }

    public Pair<Integer, PosInTerm> getPosInfo() {
        return posInfo;
    }

    public @Nullable List<String> getInsts() {
        return insts;
    }

    public ImmutableList<String> getIfSeqFormulaList() {
        return ifSeqFormulaList;
    }

    public ImmutableList<String> getIfDirectFormulaList() {
        return ifDirectFormulaList;
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
