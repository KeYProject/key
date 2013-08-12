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

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.util.Debug;

/**
 * Projection of taclet apps to the instantiation of a schema variable. The
 * projection can either be partial and undefined for those apps that do not
 * instantiate the schema variable in question, or it can raise an error for
 * such applications
 */
public class SVInstantiationProjection implements ProjectionToTerm {

    private final Name svName;
    private final boolean demandInst;
    
    private SVInstantiationProjection(Name svName, boolean demandInst) {
        this.svName = svName;
        this.demandInst = demandInst;
    }

    public static SVInstantiationProjection create(Name svName, boolean demandInst) {
        return new SVInstantiationProjection ( svName, demandInst );
    }
    
    @Override
    public Term toTerm(RuleApp app, PosInOccurrence pos, Goal goal) {
        if ( ! ( app instanceof TacletApp ) )
            Debug.fail ( "Projection is only applicable to taclet apps," +
                         " but got " + app );
       
        final TacletApp tapp = (TacletApp)app;
        final Object instObj = tapp.instantiations ().lookupValue ( svName );
        if ( ! ( instObj instanceof Term ) ) {
            Debug.assertFalse ( demandInst,
                                "Did not find schema variable "
                                + svName + " that I was supposed to examine" +
                                " (taclet " + tapp.taclet().name() + ")" );
            return null;
        }
        return (Term)instObj;
    }


}
