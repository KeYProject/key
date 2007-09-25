// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.ConstrainedFormula;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IfFormulaInstSeq;
import de.uka.ilkd.key.rule.IteratorOfIfFormulaInstantiation;
import de.uka.ilkd.key.rule.ListOfIfFormulaInstantiation;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * Binary feature that returns zero iff the <tt>\assumes</tt>- and find-formula 
 * of a Taclet are matched to different members of the sequent. If a taclet has 
 * more than one formula in its <tt>\assumes</tt> part, all of the must be matched
 *  to different members. 
 */
public class DiffFindAndIfFeature extends BinaryTacletAppFeature {
    
    /** the single instance of this feature */
    public static final Feature INSTANCE = new DiffFindAndIfFeature ();

    private DiffFindAndIfFeature () {}
    
    protected boolean filter ( TacletApp app, PosInOccurrence pos, Goal goal ) {
        assert pos != null : "Feature is only applicable to rules with find";
        
        ListOfIfFormulaInstantiation list = app.ifFormulaInstantiations();
        
        assert list != null;
                            
        final IteratorOfIfFormulaInstantiation it = list.iterator();
        while (it.hasNext()) {
            final IfFormulaInstSeq iffi = (IfFormulaInstSeq) it.next();
            assert iffi != null;
            final ConstrainedFormula findFormula = pos.constrainedFormula ();
            final ConstrainedFormula ifFormula   = iffi.getConstrainedFormula();
            
            final boolean result = pos.isInAntec () != iffi.inAntec ()
            || !findFormula.equals ( ifFormula );
            if (!result) {
                return false;
            }
        }
        return true;
    }

}
