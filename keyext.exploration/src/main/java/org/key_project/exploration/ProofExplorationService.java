/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.exploration;

import java.util.Objects;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.*;

import org.key_project.util.collection.ImmutableList;

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
 * 1) q ==> p 2) ==> p,q <-- this branch is set to interactive such that the automatic strategies do
 * not expand it Adding formulas to the succedent: '==> p' as goal node and adding q to the
 * succedent results in two branches:
 * <p>
 * 1) q ==> p <-- this branch is set to interactive such that the automatic strategies do not expand
 * it 2) ==> p,q
 *
 * @author Sarah Grebing
 * @author Alexander Weigl
 * @version 1 (20.08.19)
 */

public class ProofExplorationService {
    private final @Nonnull Proof proof;
    private final @Nonnull Services services;

    public ProofExplorationService(@Nonnull Proof proof, @Nonnull Services services) {
        this.proof = proof;
        this.services = services;
    }

    public static @Nonnull ProofExplorationService get(KeYMediator mediator) {
        return get(mediator.getSelectedProof());
    }

    private static @Nonnull ProofExplorationService get(Proof selectedProof) {
        @Nullable
        ProofExplorationService service = selectedProof.lookup(ProofExplorationService.class);
        if (service == null) {
            service = new ProofExplorationService(selectedProof, selectedProof.getServices());
            selectedProof.register(service, ProofExplorationService.class);
        }
        return service;
    }


    private Taclet getTaclet(String name) {
        return proof.getEnv().getInitConfigForEnvironment().lookupActiveTaclet(new Name(name));
    }

    private FindTaclet getHideTaclet(boolean inAntec) {
        return (FindTaclet) getTaclet(inAntec ? "hide_left" : "hide_right");
    }

    /**
     * Finds the `cut` taclet in the current proof environment.
     */
    public @Nonnull Taclet getCutTaclet() {
        return Objects.requireNonNull(
            proof.getEnv().getInitConfigForEnvironment().lookupActiveTaclet(new Name("cut")));
    }

    /**
     * Create a new Tacletapp that add a formula to the sequent using the cut rule and disabeling
     * one of the branches
     *
     * @param t Term to add to teh sequent
     * @param antecedent whether to add teh term to antecedent
     */
    public @Nonnull Node soundAddition(@Nonnull Goal g, @Nonnull Term t, boolean antecedent) {
        Taclet cut =
            g.proof().getEnv().getInitConfigForEnvironment().lookupActiveTaclet(new Name("cut"));
        Semisequent semisequent = new Semisequent(new SequentFormula(t));
        TacletApp app = NoPosTacletApp.createNoPosTacletApp(cut);
        SchemaVariable sv = app.uninstantiatedVars().iterator().next();
        app = app.addCheckedInstantiation(sv, semisequent.getFirst().formula(), services, true);
        ExplorationNodeData explorationNodeData = new ExplorationNodeData();
        if (antecedent) {
            explorationNodeData.setExplorationAction("Added " + t + " ==>");
        } else {
            explorationNodeData.setExplorationAction("Added ==> " + t);
        }

        g.node().register(explorationNodeData, ExplorationNodeData.class);

        ImmutableList<Goal> result = g.apply(app);

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

        if (first.node().getNodeInfo().getBranchLabel().endsWith(labelPostfix)) {
            first.setEnabled(false);
            toBeSelected = result.tail().head().node();
        } else {
            result.tail().head().setEnabled(false);
            toBeSelected = result.head().node();
        }
        return toBeSelected;
    }

    public Node applyChangeFormula(@Nonnull Goal g, @Nonnull PosInOccurrence pio,
            @Nonnull Term term, @Nonnull Term newTerm) {
        TacletApp app = soundChange(pio, term, newTerm);

        // taint goal with exploration
        @Nonnull
        ExplorationNodeData data = ExplorationNodeData.get(g.node());
        data.setExplorationAction(
            String.format("Edit %s to %s", LogicPrinter.quickPrintTerm(term, services),
                LogicPrinter.quickPrintTerm(newTerm, services)));

        // apply cut
        ImmutableList<Goal> result = g.apply(app);

        result.forEach(goal -> {
            ExplorationNodeData.get(goal.node()); // taint as exploration effected
            String s = goal.node().getNodeInfo().getBranchLabel();
            goal.node().getNodeInfo().setBranchLabel("ExplorationNode: " + s);
        });


        // region hide
        FindTaclet tap = getHideTaclet(pio.isInAntec());
        TacletApp weakening = PosTacletApp.createPosTacletApp(tap,
            tap.getMatcher().matchFind(pio.subTerm(), MatchConditions.EMPTY_MATCHCONDITIONS, null),
            pio, services);
        String posToWeakening = pio.isInAntec() ? "TRUE" : "FALSE";

        Node toBeSelected = null;
        for (Goal goal : result) {
            if (goal.node().getNodeInfo().getBranchLabel().contains(posToWeakening)) {
                goal.apply(weakening);
                goal.node().parent().register(new ExplorationNodeData(), ExplorationNodeData.class);
                toBeSelected = goal.node();
            } else {
                goal.setEnabled(false);
            }
        }
        return toBeSelected;
    }

    private TacletApp soundChange(@Nonnull PosInOccurrence pio, @Nonnull Term term,
            @Nonnull Term newTerm) {
        Taclet cut = getCutTaclet();
        Semisequent semisequent = new Semisequent(new SequentFormula(newTerm));
        TacletApp app = NoPosTacletApp.createNoPosTacletApp(cut);
        SchemaVariable sv = app.uninstantiatedVars().iterator().next();
        app = app.addCheckedInstantiation(sv, semisequent.getFirst().formula(), services, true);
        return app;
    }

    public void soundHide(Goal g, PosInOccurrence pio, Term term) {
        TacletApp app = createHideTerm(pio);
        ExplorationNodeData explorationNodeData = ExplorationNodeData.get(g.node());
        explorationNodeData.setExplorationAction("Hide " + term);
        ImmutableList<Goal> result = g.apply(app);
        result.forEach(goal -> ExplorationNodeData.get(goal.node()));
    }

    private TacletApp createHideTerm(PosInOccurrence pio) {
        FindTaclet tap = getHideTaclet(pio.isInAntec());
        MatchConditions match = tap.getMatcher().matchFind(pio.subTerm(),
            MatchConditions.EMPTY_MATCHCONDITIONS, services);
        return PosTacletApp.createPosTacletApp(tap, match, pio, services);
    }
}
