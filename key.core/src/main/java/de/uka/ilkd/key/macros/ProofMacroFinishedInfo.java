/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros;

import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.Statistics;
import de.uka.ilkd.key.prover.impl.ApplyStrategyInfo;
import de.uka.ilkd.key.prover.impl.DefaultTaskFinishedInfo;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * An information object with additional information about the finished proof macro. The source is
 * always a proof macro and the result is always a list of goals. This information is created and
 * passed on by every application of a proof macro as for the passed listener(s) to deal with it.
 *
 * @author Michael Kirsten
 */
public class ProofMacroFinishedInfo extends DefaultTaskFinishedInfo {

    private final Map<String, Object> proofMacroSpecificData = new HashMap<>();
    private final boolean cancelled;


    ProofMacroFinishedInfo(ProofMacro macro, ImmutableList<Goal> goals, Proof proof, long time,
            int appliedRules, int closedGoals, boolean cancelled) {
        super(macro, goals, proof, time, appliedRules, closedGoals);
        this.cancelled = cancelled;
    }

    ProofMacroFinishedInfo(ProofMacro macro, Goal goal, Proof proof, long time, int appliedRules,
            int closedGoals) {
        this(macro, ImmutableSLList.<Goal>nil().prepend(goal), proof, time, appliedRules,
            closedGoals, false);
    }

    ProofMacroFinishedInfo(ProofMacro macro, ImmutableList<Goal> goals, Proof proof,
            Statistics statistics) {
        this(macro, goals, proof, statistics == null ? 0 : statistics.timeInMillis,
            statistics == null ? 0 : statistics.totalRuleApps,
            proof == null ? 0 : (proof.countBranches() - proof.openGoals().size()), false);
    }

    ProofMacroFinishedInfo(ProofMacro macro, Goal goal, Proof proof, Statistics statistics) {
        this(macro, goal, proof, statistics == null ? 0 : statistics.timeInMillis,
            statistics == null ? 0 : statistics.totalRuleApps,
            proof == null ? 0 : (proof.countBranches() - proof.openGoals().size()));
    }

    ProofMacroFinishedInfo(ProofMacro macro, ImmutableList<Goal> goals, Proof proof,
            boolean cancelled) {
        this(macro, goals, proof, proof == null ? null : proof.getStatistics());
    }

    ProofMacroFinishedInfo(ProofMacro macro, Goal goal, Proof proof) {
        this(macro, goal, proof, proof == null ? null : proof.getStatistics());
    }

    public ProofMacroFinishedInfo(ProofMacro macro, Goal goal) {
        this(macro, goal, goal.proof());
    }

    public ProofMacroFinishedInfo(ProofMacro macro, ImmutableList<Goal> goals) {
        this(macro, goals, goals.isEmpty() ? null : goals.head().proof(), false);
    }

    public ProofMacroFinishedInfo(ProofMacro macro, Proof proof) {
        this(macro, proof.openEnabledGoals(), proof, false);
    }

    public ProofMacroFinishedInfo(ProofMacro macro, Proof proof, boolean cancelled) {
        this(macro, proof.openEnabledGoals(), proof, cancelled);
    }

    public ProofMacroFinishedInfo(ProofMacro macro, ProofMacroFinishedInfo info) {
        this(macro, info.getGoals(), info.getProof(), info.cancelled);
    }

    ProofMacroFinishedInfo(ProofMacro macro, ProofMacroFinishedInfo info,
            ImmutableList<Goal> goals) {
        this(macro, goals, info.getProof(), info.getTime(), info.getAppliedRules(),
            info.getClosedGoals(), info.cancelled);
    }

    ProofMacroFinishedInfo(ProofMacroFinishedInfo info, ApplyStrategyInfo stratInfo) {
        this(info.getMacro(), info.getGoals(), info.getProof(),
            info.getTime() + stratInfo.getTime(),
            info.getAppliedRules() + stratInfo.getAppliedRuleApps(),
            info.getClosedGoals() + stratInfo.getClosedGoals(), info.cancelled);
    }

    ProofMacroFinishedInfo(ProofMacroFinishedInfo info, ApplyStrategyInfo stratInfo,
            ImmutableList<Goal> goals) {
        this(info.getMacro(), goals, stratInfo.getProof(), info.getTime() + stratInfo.getTime(),
            info.getAppliedRules() + stratInfo.getAppliedRuleApps(),
            goals.size() <= info.getGoals().size() ? (info.getGoals().size() - goals.size()) : 0,
            false);
    }

    public void addInfo(String key, Object value) {
        proofMacroSpecificData.put(key, value);
    }

    public Object getValueFor(String key) {
        return proofMacroSpecificData.get(key);
    }

    public ProofMacro getMacro() {
        return (ProofMacro) getSource();
    }

    public boolean isCancelled() {
        return cancelled;
    }

    @SuppressWarnings("unchecked")
    public ImmutableList<Goal> getGoals() {
        final Object result = getResult();
        if (result == null) {
            return ImmutableSLList.nil();
        } else {
            return (ImmutableList<Goal>) result;
        }
    }

    public static ProofMacroFinishedInfo getDefaultInfo(ProofMacro macro, Proof proof) {
        return new ProofMacroFinishedInfo(macro, ImmutableSLList.nil(), proof, false);
    }
}
