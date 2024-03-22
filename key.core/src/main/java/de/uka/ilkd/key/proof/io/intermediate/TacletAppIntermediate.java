/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.io.intermediate;

import java.util.LinkedList;

import org.key_project.logic.Name;
import org.key_project.util.collection.ImmutableList;

/**
 * Encapsulates intermediate information for constructing a taclet application.
 *
 * @author Dominic Scheurer
 */
public class TacletAppIntermediate extends AppIntermediate {

    private String tacletName;
    private BuiltInAppIntermediate.PosInfo posInfo;
    private LinkedList<String> insts;
    private ImmutableList<String> ifSeqFormulaList;
    private ImmutableList<String> ifDirectFormulaList;
    private ImmutableList<Name> newNames;

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
    public TacletAppIntermediate(String tacletName, BuiltInAppIntermediate.PosInfo posInfo,
            LinkedList<String> insts, ImmutableList<String> ifSeqFormulaList,
            ImmutableList<String> ifDirectFormulaList, ImmutableList<Name> newNames) {
        // Taclet names are internalized later, so we don't waste memory
        this.tacletName = tacletName.intern();
        this.posInfo = posInfo;
        this.insts = insts;
        this.ifSeqFormulaList = ifSeqFormulaList;
        this.ifDirectFormulaList = ifDirectFormulaList;
        this.newNames = newNames;
    }

    public String getRuleName() {
        return tacletName;
    }

    public BuiltInAppIntermediate.PosInfo getPosInfo() {
        return posInfo;
    }

    public LinkedList<String> getInsts() {
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
     */
    @Override
    public ImmutableList<Name> getNewNames() {
        return newNames;
    }

}
