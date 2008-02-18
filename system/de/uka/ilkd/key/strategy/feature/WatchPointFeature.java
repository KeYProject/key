package de.uka.ilkd.key.strategy.feature;

import java.util.LinkedList;

import de.uka.ilkd.key.logic.ConstrainedFormula;
import de.uka.ilkd.key.logic.ListOfTerm;
import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.SLListOfTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
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
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.visualdebugger.ProofStarter;
import de.uka.ilkd.key.visualdebugger.WatchpointPO;


public class WatchPointFeature extends BinaryFeature {

    private final ListOfTerm watchpoints;

    public WatchPointFeature(ListOfTerm watchpoints) {
        super();
        this.watchpoints = watchpoints;
    }

    protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {

        assert watchpoints != null : "Watchpoints are NULL!";
        if (watchpoints.isEmpty()) {
            return false;
        } else {

            Sequent seq = goal.sequent();
            LinkedList<Update> updates = new LinkedList<Update>();
            Proof proof = goal.proof();
            UpdateFactory updateFactory = new UpdateFactory(
                    proof.getServices(), goal.simplifier());

            PIOPathIterator it = pos.iterator();
            while (it.hasNext()) {
                it.next();
                Term term = it.getSubTerm();
                Operator operator = term.op();
                if (operator instanceof QuanUpdateOperator) {

                    Update update = Update.createUpdate(term);
                    System.out.println("update.toString: " + update.toString());
                    updates.addFirst(update);
                }
            }

            TermBuilder termBuilder = new TermBuilder();

            Term watchpoint = termBuilder.or(watchpoints);
            for (Update update : updates) {
                watchpoint = updateFactory.prepend(update, watchpoint);
            }

            ConstrainedFormula newCF = new ConstrainedFormula(watchpoint);
            seq = seq.changeFormula(newCF, pos).sequent();

            // start side proof
            ProofStarter ps = new ProofStarter();

            ProofEnvironment proofEnvironment = goal.proof().env();
            InitConfig initConfig = proofEnvironment.getInitConfig();

            WatchpointPO watchpointPO = new WatchpointPO("WatchpointPO", seq);
            watchpointPO.setIndices(initConfig.createTacletIndex(), initConfig
                    .createBuiltInRuleIndex());

            StrategyProperties strategyProperties = DebuggerStrategy
                    .getDebuggerStrategyProperties(true, false, false,
                            SLListOfTerm.EMPTY_LIST);
            final StrategyFactory factory = new DebuggerStrategy.Factory();
            Strategy strategy = (factory.create(proof, strategyProperties));
            watchpointPO.setProofSettings(proof.getSettings());
            watchpointPO.setInitConfig(initConfig);
            ps.setStrategy(strategy);
            ps.setMaxSteps(500);
            ps.init(watchpointPO);
            ps.run(proofEnvironment);

            return ps.getProof().closed(); 
        }
    }

    public static WatchPointFeature create(ListOfTerm wp) {
        return new WatchPointFeature(wp);
    }
}
