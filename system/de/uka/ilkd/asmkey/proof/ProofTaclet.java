// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.proof;


import java.util.List;

import de.uka.ilkd.asmkey.util.ArrayUtil;
import de.uka.ilkd.key.logic.PosInTerm;


/** A ProofRule represents an application of an taclet. The proof rule
 * stores all required information, e.g. taclet name, selected term
 * and user instantiations.
 *
 * @author Hubert Schmid */

public final class ProofTaclet extends ProofRule {

    /** interactive instantiations */
    private final List instantiations;

    /** selected heuristics */
    private final List heuristics;

    /** formulas for if-clauses */
    private final List ifSeqFormulas;


    ProofTaclet(String name, int formula, PosInTerm pos,
              ProofInstantiation[] instantiations, boolean interactive,
              String[] heuristics, Integer[] ifSeqFormulas) {
	super(name, formula, pos, interactive);
        this.instantiations = ArrayUtil.toList(instantiations);
        this.heuristics = ArrayUtil.toList(heuristics);
        this.ifSeqFormulas = ArrayUtil.toList(ifSeqFormulas);
    }



    /** Interactive instantiations. */
    public List getInstantiations() {
        return instantiations;
    }

    /** Active heuristics */
    public List getHeuristics() {
        return heuristics;
    }

    /** formulas for if-clauses */
    public List getIfSeqFormulas() {
        return ifSeqFormulas;
    }

}
