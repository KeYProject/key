package de.uka.ilkd.key.strategy.feature;

import java.util.LinkedList;

import de.uka.ilkd.key.logic.IteratorOfTerm;
import de.uka.ilkd.key.logic.ListOfTerm;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuanUpdateOperator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.updatesimplifier.Update;

public class WatchPointFeature extends BinaryFeature {

    private ListOfTerm watchpoints = null;

    public WatchPointFeature(ListOfTerm watchpoints) {
        super();
        this.watchpoints = watchpoints;
    }

    protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {
        
        System.out.println("entering watchpointfeature...");
        LinkedList<QuanUpdateOperator> updates = new LinkedList<QuanUpdateOperator>();
                
        if (watchpoints == null || watchpoints.isEmpty()) {
            System.out.println("The list of watchpoints is empty or null.");
            return false;
        } else {
            
            System.out.println("TopLevel: " +pos.isTopLevel());
            while (!pos.isTopLevel()){
                
                System.out.println("TopLevel: " +pos.isTopLevel());
                Operator operator = pos.constrainedFormula().formula().op();
                System.out.println("operator = " + operator.getClass());               
                if (operator instanceof QuanUpdateOperator){
                    updates.add((QuanUpdateOperator) operator);  
                    System.out.println("update term ? " + pos.constrainedFormula().formula());
                    System.out.println("counted updates " + updates.size());
                }
            pos = pos.up();
            }
            //Update u = Update.createUpdate();
            IteratorOfTerm watchpointIterator = watchpoints.iterator();
            System.out.println(watchpoints.size() +" watchpoints found.");
            TermBuilder termBuilder = new TermBuilder();
            
            while (watchpointIterator.hasNext()){
                
                // U <{ boolean result;  mf(...): { result = wp; }}>result=TRUE
                Term term = watchpointIterator.next();
               // Term diamond = termFactory.createDiamondTerm(javaBlock, subTerm);
            }// -> true
            System.out.println("leaving watchpointfeature...");
            return false;
        }
    }

    public static WatchPointFeature create(ListOfTerm wp) {
        return new WatchPointFeature(wp);
    }
}
