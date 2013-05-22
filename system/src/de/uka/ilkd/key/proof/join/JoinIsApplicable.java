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

package de.uka.ilkd.key.proof.join;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;

public class JoinIsApplicable {
    public static final JoinIsApplicable INSTANCE = new JoinIsApplicable();
    
    private JoinIsApplicable() {/*It's a singleton*/}
    
    public List<ProspectivePartner> isApplicable(Goal goal ,PosInOccurrence pio){
        if(pio == null || !pio.isTopLevel() || pio.isInAntec()){
            return new LinkedList<ProspectivePartner>();
        }
        return computeProspecitvePartner(goal, pio);
    }
    
    public List<ProspectivePartner> computeProspecitvePartner(Goal goal, PosInOccurrence pio){
        assert !pio.isInAntec();
        List<ProspectivePartner> partners = new LinkedList<ProspectivePartner>();
        
        for(Goal g2 : goal.proof().openGoals()){
            if(g2 != goal){
                ProspectivePartner pair = areProspectivePartners(goal, pio, g2);
                if(pair != null){
                    partners.add(pair);
                }  
            }            
        }
        
        return partners;
    }
    
    private ProspectivePartner areProspectivePartners(Goal g1, PosInOccurrence pio ,Goal g2){
        Term referenceFormula = pio.subTerm();
     
        Term update1 = referenceFormula.op() instanceof UpdateApplication ? referenceFormula.sub(0) : TermBuilder.DF.skip();

        referenceFormula = referenceFormula.op() instanceof UpdateApplication ? referenceFormula.sub(1) : referenceFormula;
        
        
        for(SequentFormula sf : g2.sequent().succedent()){
            Term formula = sf.formula();
            Term update2 = TermBuilder.DF.skip();
            if(formula.op() instanceof UpdateApplication 
               && !formula.equals(referenceFormula)){
                    update2 = formula.sub(0);// don't change the order of this and the following line.
                    formula = formula.sub(1);
                    
            }
            if(formula.equals(referenceFormula)){
                return new ProspectivePartner(referenceFormula,g1.node(),
                        pio.constrainedFormula(),update1,g2.node(),sf,update2
                        );
            }
        }
        return null;
    }
    

    


}