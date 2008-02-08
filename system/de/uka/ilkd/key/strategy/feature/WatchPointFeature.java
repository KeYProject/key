package de.uka.ilkd.key.strategy.feature;

import java.util.LinkedList;

import de.uka.ilkd.key.logic.ConstrainedFormula;
import de.uka.ilkd.key.logic.IteratorOfTerm;
import de.uka.ilkd.key.logic.ListOfTerm;
import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.UpdateFactory;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuanUpdateOperator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.updatesimplifier.Update;
import de.uka.ilkd.key.strategy.DebuggerStrategy;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.visualdebugger.ProofStarter;
import de.uka.ilkd.key.visualdebugger.WatchpointPO;

public class WatchPointFeature extends BinaryFeature {

    private ListOfTerm watchpoints = null;

    public WatchPointFeature(ListOfTerm watchpoints) {
        super();
        this.watchpoints = watchpoints;
    }

    protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {

        System.out.println("entering watchpointfeature...");
        Sequent seq = goal.sequent();
        LinkedList<Update> updates = new LinkedList<Update>();
        Proof proof = goal.proof();
        UpdateFactory updateFactory = new UpdateFactory(proof.getServices(),
                goal.simplifier());

        assert watchpoints != null : "Watchpoints are NULL!";
        if (watchpoints==null || watchpoints.isEmpty()) {
            System.out.println("The list of watchpoints is empty.");
            return false;
        } else {
            PIOPathIterator it = pos.iterator();
            while (it.hasNext()) {
                it.next();
                Term term = it.getSubTerm();
                Operator operator = term.op();
                if (operator instanceof QuanUpdateOperator) {

                    Update update = Update.createUpdate(term);
                    System.out.println("update.toString: " + update.toString());
                    updates.add(update);

                    System.out.println("counted updates: " + updates.size());
                }
            }
            
            updates = reverseList(updates);
            IteratorOfTerm watchpointIterator = watchpoints.iterator();
            System.out.println(watchpoints.size() + " watchpoints found.");
           
            while (watchpointIterator.hasNext()) {
                Term watchpoint = watchpointIterator.next();

                for (Update update : updates) {
                    watchpoint = updateFactory.prepend(update, watchpoint);
                }
                
                ConstrainedFormula newCF = new ConstrainedFormula(watchpoint);
                seq.changeFormula(newCF, pos);
                
                // start side proof
                ProofStarter ps = new ProofStarter();
               
                StrategyProperties strategyProperties = DebuggerStrategy
                .getDebuggerStrategyProperties(true,
                        false, false, watchpoints);

                final StrategyFactory factory = new DebuggerStrategy.Factory();
                proof.setActiveStrategy((factory.create(proof, strategyProperties)));
                
                ProofEnvironment proofEnvironment = goal.proof().env();
                InitConfig initConfig = proofEnvironment.getInitConfig();
                
                WatchpointPO watchpointPO = new WatchpointPO("WatchpointPO", seq);
                watchpointPO.setIndices(initConfig.createTacletIndex(),
                        initConfig.createBuiltInRuleIndex());
                watchpointPO.setProofSettings(proof.getSettings());
                watchpointPO.setConfig(initConfig);
                ps.init(watchpointPO);
                ps.run(proofEnvironment);
            }// -> true
            
            return false;
        }
    }

    public static WatchPointFeature create(ListOfTerm wp) {
        return new WatchPointFeature(wp);
    }

    /**
     * reverseList.
     * 
     * @param updates
     *                the updates as linkedlist to reverse
     */
    private LinkedList<Update> reverseList(LinkedList<Update> updates) {

        LinkedList<Update> reversedUpdates = new LinkedList<Update>();
        for (int i = updates.size() - 1; i >= 0; i--) {
            reversedUpdates.add(updates.get(i));
        }
        return reversedUpdates;
    }
   
}
