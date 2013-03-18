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

public class FocusFormulaProjection implements ProjectionToTerm {

    public static final ProjectionToTerm INSTANCE = new FocusFormulaProjection ();
    
    private FocusFormulaProjection () {}

     public Term toTerm(RuleApp app, PosInOccurrence pos, Goal goal) {
         assert pos != null : "Projection is only applicable to rules with find";

         return pos.constrainedFormula ().formula ();
     }

}
