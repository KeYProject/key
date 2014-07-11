package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.gui.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.gui.DefaultTaskFinishedInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.Proof.Statistics;

public class ProofMacroFinishedInfo extends DefaultTaskFinishedInfo {

    ProofMacroFinishedInfo(ProofMacro macro, ImmutableList<Goal> goals,
                           Proof proof, long time, int appliedRules,
                           int closedGoals) {
        super(macro, goals, proof, time, appliedRules, closedGoals);
    }

    ProofMacroFinishedInfo(ProofMacro macro, Goal goal, Proof proof,
                           long time, int appliedRules, int closedGoals) {
        this(macro, ImmutableSLList.<Goal>nil().prepend(goal), proof,
             time, appliedRules, closedGoals);
    }

    ProofMacroFinishedInfo(ProofMacro macro, ImmutableList<Goal> goals,
            Proof proof, Statistics statistics) {
        this(macro, goals, proof,
             statistics == null ? 0 : statistics.time,
             statistics == null ? 0 : statistics.totalRuleApps,
             proof == null ? 0 : (proof.countBranches() - proof.openGoals().size()));
    }

    ProofMacroFinishedInfo(ProofMacro macro, Goal goal, Proof proof,
                           Statistics statistics) {
        this(macro, goal, proof,
             statistics == null ? 0 : statistics.time,
             statistics == null ? 0 : statistics.totalRuleApps,
             proof == null ? 0 : (proof.countBranches() - proof.openGoals().size()));
    }

    ProofMacroFinishedInfo(ProofMacro macro, ImmutableList<Goal> goals, Proof proof) {
        this(macro, goals, proof, proof == null ? null : proof.statistics());
    }

    ProofMacroFinishedInfo(ProofMacro macro, Goal goal, Proof proof) {
        this(macro, goal, proof, proof == null ? null : proof.statistics());
    }

    ProofMacroFinishedInfo(ProofMacro macro, Goal goal) {
        this(macro, goal, goal.proof());
    }

    ProofMacroFinishedInfo(ProofMacro macro, ImmutableList<Goal> goals) {
        this(macro, goals, goals.isEmpty() ? null : goals.head().proof());
    }

    ProofMacroFinishedInfo(ProofMacro macro, ProofMacroFinishedInfo info) {
        this(macro, info.getGoals(), info.getProof());
    }

    ProofMacroFinishedInfo(ProofMacroFinishedInfo info, ApplyStrategyInfo stratInfo) {
        this(info.getMacro(), stratInfo.nonCloseableGoal(), stratInfo.getProof(),
             info.getTime() + stratInfo.getTime(),
             info.getAppliedRules() + stratInfo.getAppliedRuleApps(),
             info.getClosedGoals() + stratInfo.getClosedGoals());
    }

    ProofMacroFinishedInfo setModClosedGoals(ImmutableList<Goal> goals) {
        ImmutableList<Goal> newGoals = ImmutableSLList.<Goal>nil();
        for (Goal g: goals) {
            g = getProof().getGoal(g.node());
            if (g != null) {
                newGoals = newGoals.append(g);
            }
        }
        return new ProofMacroFinishedInfo(getMacro(), newGoals, getProof(), getTime(),
                                          getAppliedRules(), getClosedGoals());
    }

    public ProofMacro getMacro() {
        return (ProofMacro)getSource();
    }

    @SuppressWarnings("unchecked")
    public ImmutableList<Goal> getGoals() {
        final Object result = getResult();
        if (result == null) {
            return ImmutableSLList.<Goal>nil();
        } else {
            return (ImmutableList<Goal>)result;
        }
    }

    public static ProofMacroFinishedInfo getDefaultInfo(ProofMacro macro, Proof proof) {
        return new ProofMacroFinishedInfo(macro, ImmutableSLList.<Goal>nil(), proof);
    }
}
