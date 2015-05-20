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

import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.util.Pair;

/**
 * TODO.
 * 
 * @author Dominic Scheurer
 */
public class TacletAppIntermediate implements AppIntermediate {

    private String tacletName = null;
    private Pair<Integer, PosInTerm> posInfo = null;
    private LinkedList<String> insts = null;
    private ImmutableList<String> ifFormulaList = null;

    public TacletAppIntermediate(String tacletName,
            Pair<Integer, PosInTerm> posInfo, LinkedList<String> insts,
            ImmutableList<String> ifFormulaList) {
        this.tacletName = tacletName;
        this.posInfo = posInfo;
        this.insts = insts;
        this.ifFormulaList = ifFormulaList;
    }

    public String getTacletName() {
        return tacletName;
    }

    public Pair<Integer, PosInTerm> getPosInfo() {
        return posInfo;
    }

    public LinkedList<String> getInsts() {
        return insts;
    }

    public ImmutableList<String> getIfFormulaList() {
        return ifFormulaList;
    }

}
