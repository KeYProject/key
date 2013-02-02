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



package de.uka.ilkd.key.strategy.termProjection;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * Projection that can store and returns an arbitrary term or formula. Objects
 * of this class are mainly used like bound variables and together with features
 * like <code>LetFeature</code> and <code>ForEachCP</code>.
 */
public class TermBuffer implements ProjectionToTerm {

    private Term t = null;
    
    public Term getContent() {
        return t;
    }

    public void setContent(Term t) {
        this.t = t;
    }

    public Term toTerm(RuleApp app, PosInOccurrence pos, Goal goal) {
        return t;
    }

}
