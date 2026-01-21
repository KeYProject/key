package org.key_project.extsourceview.utils;

import de.uka.ilkd.key.control.InteractionListener;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.ProofMacroWorker;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.macros.*;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.impl.ApplyStrategyInfo;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.settings.Settings;

import javax.swing.*;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

public class SymbolicExecutionAndSimplificationRunner {

    private final KeYMediator mediator;
    private final Node node;
    private final Node root;
    private final boolean doSimplify;
    private final boolean doTryClose;

    public SymbolicExecutionAndSimplificationRunner(KeYMediator mediator, Node node, boolean simplify, boolean tryclose) {
        this.mediator = mediator;
        this.node = node;

        var r = node;
        while (r.parent() != null) r = r.parent();
        this.root = r;

        doSimplify = simplify;
        doTryClose = tryclose;
    }

    public void runAsync() {

        FinishSymbolicExecutionMacro tcm = new FinishSymbolicExecutionMacro();

        PosInOccurrence topLevel = new PosInOccurrence(node.sequent().getFormulabyNr(1), PosInTerm.getTopLevel(), false);

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
                if (info.isCancelled()) return;

                if (doSimplify) {
                    SwingUtilities.invokeLater(() -> runSimplification());
                } else if (doTryClose) {
                    SwingUtilities.invokeLater(() -> runTryClose());
                }
            }

            @Override
            public void runBuiltInRule(Node node, IBuiltInRuleApp app, BuiltInRule rule, PosInOccurrence pos, boolean forced) {}

            @Override
            public void runAutoMode(List<Node> initialGoals, Proof proof, ApplyStrategyInfo info) { }

            @Override
            public void runRule(Node goal, RuleApp app) { }
        });

        worker.execute();
    }

    private void runSimplification() {
        var tcm = new UpdateSimplificationMacro();

        PosInOccurrence topLevel = new PosInOccurrence(root.sequent().getFormulabyNr(1), PosInTerm.getTopLevel(), false);

        final ProofMacroWorker worker = new ProofMacroWorker(root, tcm, mediator, topLevel);
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
                if (info.isCancelled()) return;

                if (doTryClose) {
                    SwingUtilities.invokeLater(() -> runTryClose());
                }
            }

            @Override
            public void runBuiltInRule(Node node, IBuiltInRuleApp app, BuiltInRule rule, PosInOccurrence pos, boolean forced) {}

            @Override
            public void runAutoMode(List<Node> initialGoals, Proof proof, ApplyStrategyInfo info) { }

            @Override
            public void runRule(Node goal, RuleApp app) { }
        });

        worker.execute();
    }

    private void runTryClose() {
        var tcm = new TryCloseMacro(Integer.getInteger("key.autopilot.closesteps", 3000));

        PosInOccurrence topLevel = new PosInOccurrence(root.sequent().getFormulabyNr(1), PosInTerm.getTopLevel(), false);

        final ProofMacroWorker worker = new ProofMacroWorker(root, tcm, mediator, topLevel);
        mediator.stopInterface(true);
        mediator.setInteractive(false);
        mediator.addInterruptedListener(worker);

        worker.execute();
    }

    public boolean canApply() {
        var containsJava1 = node.sequent().succedent().asList().stream().anyMatch(p -> p.formula().containsJavaBlockRecursive());
        var containsJava2 = node.sequent().antecedent().asList().stream().anyMatch(p -> p.formula().containsJavaBlockRecursive());

        var topLevel = new PosInOccurrence(node.sequent().getFormulabyNr(1), PosInTerm.getTopLevel(), false);

        return (containsJava1 || containsJava2) && (new FinishSymbolicExecutionMacro()).canApplyTo(node, topLevel);
    }
}
