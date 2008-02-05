package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.IteratorOfExpression;
import de.uka.ilkd.key.java.ListOfExpression;
import de.uka.ilkd.key.logic.IteratorOfTerm;
import de.uka.ilkd.key.logic.ListOfTerm;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;

public class WatchPointFeature extends BinaryFeature {

    private ListOfTerm watchpoints = null;

    public WatchPointFeature(ListOfTerm watchpoints) {
        super();
        this.watchpoints = watchpoints;
    }

    protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {
        
        System.out.println("entering watchpointfeature...");
        Sequent seq =  goal.sequent(); 

        if (watchpoints == null || watchpoints.isEmpty()) {
            System.out.println("The list of watchpoints is empty or null.");
            return false;
        } else {
            
            IteratorOfTerm watchpointIterator = watchpoints.iterator();
            System.out.println(watchpoints.size() +" watchpoints found.");
            TermBuilder termBuilder = new TermBuilder();
            
            while (watchpointIterator.hasNext()){
                
                // U <{ boolean result;  mf(...): { result = wp; }}>result=TRUE
                Term term = watchpointIterator.next();
               // Term diamond = termFactory.createDiamondTerm(javaBlock, subTerm);
                  
                
                

            }// -> true
            return false;
        }
    }

    public static WatchPointFeature create(ListOfTerm wp) {
        return new WatchPointFeature(wp);
    }
}
