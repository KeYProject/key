package de.uka.ilkd.key.strategy.feature;

import java.util.LinkedList;

import de.uka.ilkd.key.logic.IteratorOfTerm;
import de.uka.ilkd.key.logic.ListOfTerm;
import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.UpdateFactory;
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
        LinkedList<Update> updates = new LinkedList<Update>();
        UpdateFactory updateFactory = new UpdateFactory(goal.proof().getServices(),goal.simplifier());

        assert watchpoints != null : "Watchpoints are NULL!";
        if (watchpoints.isEmpty()) {
            System.out.println("The list of watchpoints is empty.");
            return false;
        } else {
                PIOPathIterator it = pos.iterator();
                while(it.hasNext()){
                    it.next();
                    Term term = it.getSubTerm();
                    Operator operator = term.op();
                    if (operator instanceof QuanUpdateOperator) {
                        
                        Update update = Update.createUpdate(term);
                        System.out.println("update.toString: "+update.toString());
                        updates.add(update);
                      
                        System.out.println("counted updates: " + updates.size());
                    }
                }
            
            IteratorOfTerm watchpointIterator = watchpoints.iterator();
            System.out.println(watchpoints.size() + " watchpoints found.");

            while (watchpointIterator.hasNext()) {

                Term watchpoint = watchpointIterator.next();
                for (Update update : updates) {
                    updateFactory.prepend(update, watchpoint);
                }
                //start side proof
            }// -> true
            System.out.println("leaving watchpointfeature...");
            return false;
        }
    }

    public static WatchPointFeature create(ListOfTerm wp) {
        return new WatchPointFeature(wp);
    }
}
