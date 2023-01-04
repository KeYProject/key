package org.key_project.extsourceview.utils;

import de.uka.ilkd.key.control.InteractionListener;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.ProofMacroWorker;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.macros.FinishSymbolicExecutionMacro;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.macros.UpdateSimplificationMacro;
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

    private List<Node> simplificationNodes;

    public SymbolicExecutionAndSimplificationRunner(KeYMediator mediator, Node node) {
        this.mediator = mediator;
        this.node = node;
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

                Iterable<Node> iter = node::leavesIterator;
                simplificationNodes = StreamSupport.stream(iter.spliterator(), false).collect(Collectors.toList());

                SwingUtilities.invokeLater(() -> runSimplification());
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
        if (simplificationNodes.isEmpty()) return;

        var node = simplificationNodes.remove(0);

        var tcm = new UpdateSimplificationMacro();

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
                SwingUtilities.invokeLater(() -> runSimplification());
            }

            @Override
            public void runBuiltInRule(Node node, IBuiltInRuleApp app, BuiltInRule rule, PosInOccurrence pos, boolean forced) { }

            @Override
            public void runAutoMode(List<Node> initialGoals, Proof proof, ApplyStrategyInfo info) { }

            @Override
            public void runRule(Node goal, RuleApp app) { }
        });

        worker.execute();
    }

    public boolean canApply() {
        var containsJava1 = node.sequent().succedent().asList().stream().anyMatch(p -> p.formula().containsJavaBlockRecursive());
        var containsJava2 = node.sequent().antecedent().asList().stream().anyMatch(p -> p.formula().containsJavaBlockRecursive());

        var topLevel = new PosInOccurrence(node.sequent().getFormulabyNr(1), PosInTerm.getTopLevel(), false);

        return (containsJava1 || containsJava2) && (new FinishSymbolicExecutionMacro()).canApplyTo(node, topLevel);
    }
}
