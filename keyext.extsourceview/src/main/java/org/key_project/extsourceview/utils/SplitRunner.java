package org.key_project.extsourceview.utils;

import de.uka.ilkd.key.control.InteractionListener;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.ProofMacroWorker;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.macros.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.settings.Settings;
import org.key_project.logic.PosInTerm;
import org.key_project.prover.engine.ProofSearchInformation;
import org.key_project.prover.engine.impl.ApplyStrategyInfo;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

import javax.swing.*;
import java.util.List;

public class SplitRunner {

    private final KeYMediator mediator;
    private final Node node;
    private final boolean doSimplify;
    private final boolean doTryClose;

    public SplitRunner(KeYMediator mediator, Node node, boolean simplify, boolean tryclose) {
        this.mediator = mediator;
        this.node = node;

        doSimplify = simplify;
        doTryClose = tryclose;
    }

    public void runAsync(ImmutableList<PosInOccurrence> pios) {

        FullPropositionalExpansionMacro tcm = new FullPropositionalExpansionMacro();

        final ProofMacroWorker worker = new ProofMacroWorker(node, tcm, mediator, pios.head().topLevel());
        mediator.stopInterface(true);
        mediator.setInteractive(false);
        mediator.addInterruptedListener(worker);

        worker.addInteractionListener(new InteractionListener() {
            @Override
            public void settingChanged(Proof proof, Settings settings, SettingType type, String message) { }

            @Override
            public void runPrune(Node node) { }

            @Override
            public void runMacro(Node node, ProofMacro macro, PosInOccurrence posInOcc, ProofMacroFinishedInfo info) {
                // TODO: WP: check
                //if (info.isCancelled()) return;

                if (doSimplify) {
                    SwingUtilities.invokeLater(() -> runSimplification());
                } else if (doTryClose) {
                    SwingUtilities.invokeLater(() -> runTryClose());
                }
            }

            @Override
            public void runBuiltInRule(Node node, IBuiltInRuleApp app, BuiltInRule rule, PosInOccurrence pos, boolean forced) {}

            @Override
            public void runAutoMode(List<Node> initialGoals, Proof proof,
                                    ProofSearchInformation<Proof, Goal> info) {
            }

            @Override
            public void runRule(Node goal, RuleApp app) { }
        });

        worker.execute();
    }

    private void runSimplification() {
        var tcm = new UpdateSimplificationMacro();

        PosInOccurrence topLevel = new PosInOccurrence(node.sequent().getFormulaByNr(1), PosInTerm.getTopLevel(), false);

        final ProofMacroWorker worker = new ProofMacroWorker(node, tcm, mediator, topLevel);
        mediator.stopInterface(true);
        mediator.setInteractive(false);
        mediator.addInterruptedListener(worker);

        worker.addInteractionListener(new InteractionListener() {
            @Override
            public void settingChanged(Proof proof, Settings settings, SettingType type, String message) { }

            @Override
            public void runPrune(Node node) { }

            @Override
            public void runMacro(Node node, ProofMacro macro, PosInOccurrence posInOcc, ProofMacroFinishedInfo info) {
                // TODO: WP: check
                //if (info.isCancelled()) return;

                if (doTryClose) {
                    SwingUtilities.invokeLater(() -> runTryClose());
                }
            }

            @Override
            public void runBuiltInRule(Node node, IBuiltInRuleApp app, BuiltInRule rule, PosInOccurrence pos, boolean forced) {}

            @Override
            public void runAutoMode(List<Node> initialGoals, Proof proof,
                                    ProofSearchInformation<Proof, Goal> info) {
            }

            @Override
            public void runRule(Node goal, RuleApp app) { }
        });

        worker.execute();
    }

    private void runTryClose() {
        var tcm = new TryCloseMacro(Integer.getInteger("key.autopilot.closesteps", 3000));

        PosInOccurrence topLevel = new PosInOccurrence(node.sequent().getFormulaByNr(1), PosInTerm.getTopLevel(), false);

        final ProofMacroWorker worker = new ProofMacroWorker(node, tcm, mediator, topLevel);
        mediator.stopInterface(true);
        mediator.setInteractive(false);
        mediator.addInterruptedListener(worker);

        worker.execute();
    }

    public boolean canApply(ImmutableList<PosInOccurrence> pios) {
        if (pios == null) {
            return false;
        }
        if (pios.isEmpty()) {
            return false;
        }
        if (!(new FullPropositionalExpansionMacro()).canApplyTo(mediator.getSelectedNode(), pios.head().topLevel())) {
            return false;
        }
        if (pios.head().topLevel().subTerm().op() != Junctor.AND) {
            return false;
        }
        if (pios.head().isInAntec()) {
            return false;
        }
        return true;
    }
}
