// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Metavariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * Feature that returns zero if and only if the focus of the application in
 * question is not a metavariable or if the find-expression of the taclet only
 * is a single schema variable
 */
public class NotWithinMVFeature extends BinaryTacletAppFeature {

    public static Feature INSTANCE = new NotWithinMVFeature ();
    
    private NotWithinMVFeature () {}
    
    protected boolean filter(TacletApp app, PosInOccurrence pos, Goal goal) {
        if ( pos == null ) return true;
        
        if ( ! ( pos.subTerm ().op () instanceof Metavariable ) ) return true;

        final FindTaclet t = (FindTaclet)app.taclet ();
        final Term findExpr = t.find ();
        return findExpr.op () instanceof SchemaVariable;
    }

}
