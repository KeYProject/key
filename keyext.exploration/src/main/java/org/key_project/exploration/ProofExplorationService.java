/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.exploration;


import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.rule.*;

import org.key_project.logic.Name;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.TacletMatcher;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * ExplorationAction that handles the addition of formulas to the sequent. This action is
 * implemented using the cut rule.
 * <p>
 * The branch not corresponding to the desried change is set to interactive. This enables that the
 * automatic strategies avoid expanding this branch and the user needs to activate the branch by
 * hand.
 * <p>
 * Adding formulas to the antecedent: '==> p' as goal node and adding q to the antecedent results in
 * two branches:
 * <p>
 * <ol>
 * <li>{@code q ==> p}</li>
 * <li>{@code ==> p,q} {@code <--} this branch is set to interactive such that the automatic
 * strategies do
 * not expand it.</li>
 * </ol>
 * Adding formulas to the succedent: '==> p' as goal node and adding q to the
 * succedent results in two branches:
 * </ol>
 * <p>
 * <ol>
 * <li>{@code q ==> p} {@code <--} this branch is set to interactive such that the automatic
 * strategies do not expand
 * it</li>
 * <li>{@code ==> p,q}</li>
 * </ol>
 *
 * @author Sarah Grebing
 * @author Alexander Weigl
 * @version 1 (20.08.19)
 */

@NullMarked
@SuppressWarnings("ClassCanBeRecord")
public class ProofExplorationService {
    private final @NonNull Proof proof;
    private final @NonNull Services services;

    public ProofExplorationService(@NonNull Proof proof, @NonNull Services services) {
        this.proof = proof;
        this.services = services;
    }

    public static @NonNull ProofExplorationService get(KeYMediator mediator) {
        Proof selectedProof = mediator.getSelectedProof();
        if (selectedProof == null) {
            throw new NullPointerException("No proof selected.");
        }
        return get(selectedProof);
    }

    private static @NonNull ProofExplorationService get(Proof selectedProof) {
        @Nullable
        ProofExplorationService service = selectedProof.lookup(ProofExplorationService.class);
        if (service == null) {
            service = new ProofExplorationService(selectedProof, selectedProof.getServices());
            selectedProof.register(service, ProofExplorationService.class);
        }
        return service;
    }


    private Taclet getTaclet(String name) {
        ProofEnvironment env = proof.getEnv();
        if (env == null) {
            throw new NullPointerException("Proof has no proof environment: " + proof);
        }
        Taclet taclet = env.getInitConfigForEnvironment().lookupActiveTaclet(new Name(name));
        if (taclet == null) {
            throw new NullPointerException("No active taclet '" + name + "' in " + proof);
        }
        return taclet;
    }

    private FindTaclet getHideTaclet(boolean inAntec) {
        return (FindTaclet) getTaclet(inAntec ? "hide_left" : "hide_right");
    }

    /**
     * Finds the `cut` taclet in the current proof environment.
     */
    public @NonNull Taclet getCutTaclet() {
        ProofEnvironment env = proof.getEnv();
        if (env == null) {
            throw new NullPointerException("Proof has no proof environment: " + proof);
        }
        Taclet cut = env.getInitConfigForEnvironment().lookupActiveTaclet(new Name("cut"));
        if (cut == null) {
            throw new NullPointerException("No active 'cut' taclet in " + proof);
        }
        return cut;
    }

    /**
     * Create a new Tacletapp that add a formula to the sequent using the cut rule and disabeling
     * one of the branches
     *
     * @param t Term to add to teh sequent
     * @param antecedent whether to add teh term to antecedent
     */
    public @NonNull Node soundAddition(@NonNull Goal g, @NonNull JTerm t, boolean antecedent) {
        ProofEnvironment env = g.proof().getEnv();
        if (env == null) {
            throw new NullPointerException("Proof has no proof environment: " + g.proof());
        }
        Taclet cut = env.getInitConfigForEnvironment().lookupActiveTaclet(new Name("cut"));
        if (cut == null) {
            throw new NullPointerException("No active 'cut' taclet in " + g.proof());
        }
        TacletApp app = NoPosTacletApp.createNoPosTacletApp(cut);
        SchemaVariable sv = app.uninstantiatedVars().iterator().next();
        TacletApp instantiated = app.addCheckedInstantiation(sv, t, services, true);
        if (instantiated == null) {
            throw new NullPointerException("Could not instantiate the 'cut' taclet with " + t);
        }
        app = instantiated;
        ExplorationNodeData explorationNodeData = new ExplorationNodeData();
        if (antecedent) {
            explorationNodeData.setExplorationAction("Added " + t + " ==>");
        } else {
            explorationNodeData.setExplorationAction("Added ==> " + t);
        }

        g.node().register(explorationNodeData, ExplorationNodeData.class);

        ImmutableList<Goal> applied = g.apply(app);
        if (applied == null) {
            throw new NullPointerException("Could not apply the 'cut' rule to " + g);
        }
        ImmutableList<Goal> result = applied;

        // set the actions flag
        result.forEach(goal -> {
            goal.node().register(new ExplorationNodeData(), ExplorationNodeData.class);
            String s = goal.node().getNodeInfo().getBranchLabel();
            goal.node().getNodeInfo().setBranchLabel("ExplorationNode: " + s);
        });

        assert result.size() == 2;
        Node toBeSelected;
        String labelPostfix = antecedent ? "FALSE" : "TRUE";
        Goal first = result.head();

        String branchLabel = first.node().getNodeInfo().getBranchLabel();
        if (branchLabel == null) {
            throw new NullPointerException(
                "First goal of the cut application has no branch label.");
        }
        if (branchLabel.endsWith(labelPostfix)) {
            first.setEnabled(false);
            toBeSelected = result.tail().head().node();
        } else {
            result.tail().head().setEnabled(false);
            toBeSelected = result.head().node();
        }
        return toBeSelected;
    }

    public @Nullable Node applyChangeFormula(@NonNull Goal g,
            @NonNull PosInOccurrence pio,
            @NonNull JTerm term, @NonNull JTerm newTerm) {
        TacletApp app = soundChange(pio, term, newTerm);

        // taint goal with exploration
        @NonNull
        ExplorationNodeData data = ExplorationNodeData.get(g.node());
        data.setExplorationAction(
            String.format("Edit %s to %s", LogicPrinter.quickPrintTerm(term, services),
                LogicPrinter.quickPrintTerm(newTerm, services)));

        // apply cut
        ImmutableList<Goal> applied = g.apply(app);
        if (applied == null) {
            throw new NullPointerException("Could not apply the change ('cut') rule to " + g);
        }
        ImmutableList<Goal> result = applied;

        result.forEach(goal -> {
            ExplorationNodeData.get(goal.node()); // taint as exploration effected
            String s = goal.node().getNodeInfo().getBranchLabel();
            goal.node().getNodeInfo().setBranchLabel("ExplorationNode: " + s);
        });


        // region hide
        FindTaclet tap = getHideTaclet(pio.isInAntec());
        TacletMatcher matcher = tap.getMatcher();
        if (matcher == null) {
            throw new NullPointerException("The taclet '" + tap.name() + "' has no matcher.");
        }
        MatchResultInfo matchingConditions = matcher.matchFind(pio.subTerm(),
            MatchConditions.EMPTY_MATCHCONDITIONS, services);
        if (matchingConditions == null) {
            throw new NullPointerException(
                "Could not match the find term of '" + tap.name() + "'.");
        }
        TacletApp weakening = PosTacletApp.createPosTacletApp(tap, matchingConditions, pio,
            services);
        if (weakening == null) {
            throw new NullPointerException("Could not create the weakening rule application.");
        }
        String posToWeakening = pio.isInAntec() ? "TRUE" : "FALSE";

        Node toBeSelected = null;
        for (Goal goal : result) {
            String branchLabel = goal.node().getNodeInfo().getBranchLabel();
            if (branchLabel == null) {
                throw new NullPointerException(
                    "Goal of the change application has no branch label.");
            }
            if (branchLabel.contains(posToWeakening)) {
                goal.apply(weakening);
                Node parent = goal.node().parent();
                if (parent == null) {
                    throw new NullPointerException("The weakening goal has no parent node.");
                }
                parent.register(new ExplorationNodeData(), ExplorationNodeData.class);
                toBeSelected = goal.node();
            } else {
                goal.setEnabled(false);
            }
        }
        return toBeSelected;
    }

    private TacletApp soundChange(@NonNull PosInOccurrence pio,
            @NonNull JTerm term,
            @NonNull JTerm newTerm) {
        Taclet cut = getCutTaclet();
        TacletApp app = NoPosTacletApp.createNoPosTacletApp(cut);
        SchemaVariable sv = app.uninstantiatedVars().iterator().next();
        TacletApp instantiated = app.addCheckedInstantiation(sv, newTerm, services, true);
        if (instantiated == null) {
            throw new NullPointerException(
                "Could not instantiate the 'cut' taclet with " + newTerm);
        }
        return instantiated;
    }

    public void soundHide(Goal g, PosInOccurrence pio, JTerm term) {
        TacletApp app = createHideTerm(pio);
        ExplorationNodeData explorationNodeData = ExplorationNodeData.get(g.node());
        explorationNodeData.setExplorationAction("Hide " + term);
        ImmutableList<Goal> applied = g.apply(app);
        if (applied == null) {
            throw new NullPointerException("Could not apply the hide rule to " + g);
        }
        applied.forEach(goal -> ExplorationNodeData.get(goal.node()));
    }

    private TacletApp createHideTerm(PosInOccurrence pio) {
        FindTaclet tap = getHideTaclet(pio.isInAntec());
        TacletMatcher matcher = tap.getMatcher();
        if (matcher == null) {
            throw new NullPointerException("The taclet '" + tap.name() + "' has no matcher.");
        }
        MatchResultInfo matchingConditions = matcher.matchFind(pio.subTerm(),
            MatchConditions.EMPTY_MATCHCONDITIONS, services);
        if (matchingConditions == null) {
            throw new NullPointerException(
                "Could not match the find term of '" + tap.name() + "'.");
        }
        TacletApp app = PosTacletApp.createPosTacletApp(tap, matchingConditions, pio, services);
        if (app == null) {
            throw new NullPointerException("Could not create the hide rule application.");
        }
        return app;
    }
}
