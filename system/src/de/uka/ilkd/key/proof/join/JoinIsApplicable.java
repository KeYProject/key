package de.uka.ilkd.key.proof.join;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
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
        Term formula1 = referenceFormula;
        referenceFormula = referenceFormula.op() instanceof UpdateApplication ? referenceFormula.sub(1) : referenceFormula;
        
        
        for(SequentFormula sf : g2.sequent().succedent()){
            Term formula = sf.formula();
            Term formula2 = formula;
            Term update2 = TermBuilder.DF.skip();
            if(formula.op() instanceof UpdateApplication 
               && !formula.equals(referenceFormula)){
                    update2 = formula.sub(0);// don't change the order of this and the following line.
                    formula = formula.sub(1);
                    
            }
            if(formula.equals(referenceFormula)){
                return new ProspectivePartner(referenceFormula,g1.node(),formula1,update1,pio,g2.node(),formula2,update2,
                        new PosInOccurrence(sf,PosInTerm.TOP_LEVEL,false));
            }
        }
        return null;
    }
    

    


}
