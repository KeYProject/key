// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.WaryClashFreeSubst;


public final class WarySubstOp extends SubstOp {

    /** the wary substitution operator {var<-term}'. {x<-d}'A(x) means
     * replace all free occurrences of variable x in A with d, however
     * without replacing x with a non-rigid A below modalities */
    public static final SubstOp SUBST = new WarySubstOp(new Name("subst"));


    private WarySubstOp(Name name) {
	super(name);
    }


    @Override
    public Term apply ( Term term, TermServices services ) {
	QuantifiableVariable v=term.varsBoundHere(1).get(0);
	WaryClashFreeSubst cfSubst = new WaryClashFreeSubst(v, term.sub(0), services);
	return cfSubst.apply(term.sub(1));
    }
}