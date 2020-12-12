package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.ProverCore;
import de.uka.ilkd.key.prover.ProverTaskListener;
import de.uka.ilkd.key.prover.impl.ApplyStrategy;
import de.uka.ilkd.key.prover.impl.ApplyStrategyInfo;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.RuleSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

public class LimitedRuleSetsMacro extends AbstractPropositionalExpansionMacro {
    private final List<RuleSet> allowedRuleSets = new LinkedList<>();
    private final Set<String> admittedRules = new HashSet<>();
    private final int numSteps;

    public LimitedRuleSetsMacro(Goal goal, int numSteps, String[] allowedRuleSetsNames) {
        this.numSteps = numSteps;
        for (String name : allowedRuleSetsNames) {
            this.allowedRuleSets.add(new RuleSet(new Name(name)));
        }
        // Collect all admitted rules for the allowed rule sets:
        // Note that the rules are only collected once at creation. If rules are added to the taclet
        // index afterwards, those are not in the list of admitted rules!
        Set<NoPosTacletApp> allTaclets = goal.indexOfTaclets().allNoPosTacletApps();
        for (NoPosTacletApp npa : allTaclets) {
            ImmutableList<RuleSet> tacletRuleSets = npa.taclet().getRuleSets();
            for (RuleSet allowed : allowedRuleSets) {
                if (tacletRuleSets.contains(allowed)) {
                    admittedRules.add(npa.taclet().name().toString());
                }
            }
        }
    }

    @Override
    public ProofMacroFinishedInfo applyTo(UserInterfaceControl uic, Proof proof,
                                          ImmutableList<Goal> goals, PosInOccurrence posInOcc,
                                          ProverTaskListener listener) throws InterruptedException {
        if (goals == null || goals.isEmpty()) {
            // should not happen, because in this case canApplyTo returns false
            return null;
        }

        // create the rule application engine
        final ProverCore applyStrategy =
            new ApplyStrategy(proof.getServices().getProfile().getSelectedGoalChooserBuilder().create());
        // assert: all goals have the same proof

        final ImmutableList<Goal> ignoredOpenGoals = setDifference(proof.openGoals(), goals);
        ProofMacroFinishedInfo info =
            new ProofMacroFinishedInfo(this, goals, proof, 0, 0, 0, false);

        //
        // start actual autoprove
        try {
            for (final Goal goal : goals) {
                Node node = goal.node();
                int maxSteps = numSteps > 0 ? numSteps : proof.getSettings().getStrategySettings().getMaxSteps();
                final ApplyStrategyInfo result =
                    applyStrategy.start(proof, ImmutableSLList.<Goal>nil().prepend(goal),
                        maxSteps, -1, false);
                //final Goal closedGoal;

                // retreat if not closed
                if(!node.isClosed()) {
                    proof.pruneProof(node);
                    //closedGoal = null;
                } else {
                    //closedGoal = goal;
                }

                synchronized(applyStrategy) { // wait for applyStrategy to finish its last rule application
                    info = new ProofMacroFinishedInfo(info, result);
                    if(applyStrategy.hasBeenInterrupted()) { // only now reraise the interruption exception
                        throw new InterruptedException();
                    }
                }
            }
        } finally {
            final ImmutableList<Goal> resultingGoals = setDifference(proof.openGoals(), ignoredOpenGoals);
            info = new ProofMacroFinishedInfo(this, info, resultingGoals);
        }
        return info;
    }

    @Override
    protected Set<String> getAdmittedRuleNames() {
        return admittedRules;
    }

    @Override
    protected boolean allowOSS() {
        return false;
    }

    @Override
    public String getName() {
        StringBuilder sb = new StringBuilder("LimitedRuleSetsMacro (");
        for (RuleSet rs : allowedRuleSets) {
            sb.append(rs.name());
            sb.append(", ");
        }
        sb.delete(sb.length() - 2, sb.length());
        sb.append(")");
        return sb.toString();
    }

    @Override
    public String getDescription() {
        return null;
    }
}
