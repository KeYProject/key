// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2015 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof.io.intermediate;

import java.util.LinkedList;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.util.Pair;

/**
 * Encapsulates intermediate information for constructing a taclet application.
 * 
 * @author Dominic Scheurer
 */
public class TacletAppIntermediate extends AppIntermediate {

    private String tacletName = null;
    private Pair<Integer, PosInTerm> posInfo = null;
    private LinkedList<String> insts = null;
    private ImmutableList<String> ifSeqFormulaList = null;
    private ImmutableList<String> ifDirectFormulaList = null;
    private ImmutableList<Name> newNames = null;

    /**
     * Constructs a new intermediate taclet application.
     *
     * @param tacletName Name of the taclet.
     * @param posInfo Position information (Integer representing position
     *   of the target formula, PosInTerm for relevant term inside the formula).
     * @param insts Schema variable instantiations.
     * @param ifSeqFormulaList
     * @param ifDirectFormulaList
     * @param newNames New names registered during taclet application.
     */
    public TacletAppIntermediate(String tacletName,
            Pair<Integer, PosInTerm> posInfo, LinkedList<String> insts,
            ImmutableList<String> ifSeqFormulaList, ImmutableList<String> ifDirectFormulaList,
            ImmutableList<Name> newNames) {
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

    public Pair<Integer, PosInTerm> getPosInfo() {
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

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.io.intermediate.AppIntermediate#getNewNames()
     */
    @Override
    public ImmutableList<Name> getNewNames() {
        return newNames;
    }

}
