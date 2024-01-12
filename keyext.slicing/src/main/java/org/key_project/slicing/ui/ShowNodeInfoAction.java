/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing.ui;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;

import org.key_project.slicing.DependencyTracker;
import org.key_project.slicing.analysis.AnalysisResults;
import org.key_project.slicing.graph.AnnotatedEdge;
import org.key_project.slicing.graph.GraphNode;

/**
 * Context menu action to show information on a dependency graph node (incoming / outgoing edges).
 * Used only for debugging purposes.
 *
 * @author Arne Keller
 */
public class ShowNodeInfoAction extends MainWindowAction {

    private static final long serialVersionUID = -1878750240016534264L;

    /**
     * Dependency tracker, used to get the information to display in the dialog.
     */
    private final transient DependencyTracker tracker;

    /**
     * The graph node to show information on.
     */
    private final transient GraphNode node;

    /**
     * Construct a new debug dialog. Call {@link #showDialog(Window)} afterwards to make it visible
     * to the user.
     *
     * @param mw main window
     * @param tracker dependency tracker
     * @param node node to show info on
     */
    public ShowNodeInfoAction(MainWindow mw, DependencyTracker tracker, GraphNode node) {
        super(mw);
        setName("Show dependency graph info");
        this.tracker = tracker;
        this.node = node;
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        showDialog(MainWindow.getInstance());
    }

    /**
     * Show a dialog with dependency graph information on the {@link #node}.
     *
     * @param parentWindow the parent window to center this dialog on
     */
    private void showDialog(Window parentWindow) {
        List<GraphNode> graphNodes = new ArrayList<>();
        List<Node> proofSteps = new ArrayList<>();
        AnalysisResults analysisResults = tracker.getAnalysisResults();
        Function<Triple<Node, GraphNode, AnnotatedEdge>, Collection<String>> nodeToTableRow = n -> {
            proofSteps.add(n.first);
            graphNodes.add(n.second);
            var ruleName = n.first.getAppliedRuleApp().rule().displayName();
            return List.of(
                Integer.toString(n.first.serialNr()),
                analysisResults != null && !analysisResults.usefulSteps.contains(n.first)
                        ? "<strike>" + ruleName + "</strike>"
                        : ruleName,
                n.third.replacesInputNode() ? "yes" : "no",
                n.second.toString(false, false));
        };
        var idxFactory = new IndexFactory();

        var headers1 = List.of("Serial Nr.", "Rule name", "Consumed", "Used formula");
        var headers2 = List.of("Serial Nr.", "Rule name", "Consumed", "Produced formula");
        var clickable = new boolean[] { false, true, false, true };
        var incoming = tracker.getDependencyGraph()
                .incomingGraphEdgesOf(node).map(nodeToTableRow).collect(Collectors.toList());
        var outgoing = tracker.getDependencyGraph()
                .outgoingGraphEdgesOf(node).map(nodeToTableRow).collect(Collectors.toList());
        var html1 =
            HtmlFactory.generateTable(headers1, clickable, Optional.empty(), incoming, idxFactory);
        var html2 =
            HtmlFactory.generateTable(headers2, clickable, Optional.empty(), outgoing, idxFactory);
        var useful = analysisResults != null
                ? tracker.getDependencyGraph().outgoingGraphEdgesOf(node)
                        .filter(t -> analysisResults.usefulSteps.contains(t.first)).count()
                : -1;
        var extraInfo = useful != -1 ? "<h2>" + useful + " useful rule apps</h2>" : "";
        var previousDerivations = 0;
        var graphNode = node;
        while (!graphNode.getBranchLocation().isEmpty()) {
            graphNode = graphNode.popLastBranchID();
            if (tracker.getDependencyGraph().containsNode(graphNode)) {
                previousDerivations++;
            }
        }
        var html = "<h1>Produced by</h1>" + html1
            + "<h1>This node</h1>" + "<p>" + node.toString(false, false) + "</p>"
            + "<p><small>" + previousDerivations + "x derived in previous branches" + "</small></p>"
            + "<p><small>" + "Identity: " + System.identityHashCode(node) + "</small></p>"
            + "<h1>Used by</h1>"
            + extraInfo
            + html2
            + "<p>strikethrough rule name = useless rule app</p>";
        new HtmlDialog(parentWindow,
            "Dependency graph node info", html, event -> {
                var parts = event.substring(1).split("_");
                var column = Integer.parseInt(parts[0]);
                var idx = Integer.parseInt(parts[1]);
                if (column == 1) {
                    showDialogForStep(parentWindow, proofSteps.get(idx / 2));
                } else {
                    new ShowNodeInfoAction(mainWindow, tracker, graphNodes.get(idx / 2))
                            .showDialog(parentWindow);
                }
            });
    }

    private void showDialogForStep(Window parentWindow, Node proofStep) {
        var graphNodes = new ArrayList<GraphNode>();
        var analysisResults = tracker.getAnalysisResults();
        var idxFactory = new IndexFactory();

        var headers1 = List.of("Consumed", "Used formula");
        var headers2 = List.of("Produced formula");
        var clickable = new boolean[] { false, true };
        var clickable2 = new boolean[] { true };
        var depGraph = tracker.getDependencyGraph();
        var inputs = depGraph
                .edgesOf(proofStep)
                .stream()
                .map(x -> new Pair<>(depGraph.inputOf(x), x.replacesInputNode()))
                .collect(Collectors.toSet())
                .stream()
                .map(n -> {
                    graphNodes.add(n.first);
                    var label = n.first.toString(false, false);
                    return (Collection<String>) List.of(
                        n.second.toString(),
                        analysisResults != null && !analysisResults.usefulNodes.contains(n.first)
                                ? "<strike>" + label + "</strike>"
                                : label);
                })
                .collect(Collectors.toList());
        var outputs = depGraph
                .edgesOf(proofStep)
                .stream()
                .map(x -> new Pair<>(depGraph.outputOf(x), x.replacesInputNode()))
                .collect(Collectors.toSet())
                .stream()
                .map(n -> {
                    graphNodes.add(n.first);
                    var label = n.first.toString(false, false);
                    return (Collection<String>) List.of(
                        analysisResults != null && !analysisResults.usefulNodes.contains(n.first)
                                ? "<strike>" + label + "</strike>"
                                : label);
                })
                .collect(Collectors.toList());
        var html1 =
            HtmlFactory.generateTable(headers1, clickable, Optional.empty(), inputs, idxFactory);
        var html2 =
            HtmlFactory.generateTable(headers2, clickable2, Optional.empty(), outputs, idxFactory);
        var html = "<h1>Inputs</h1>"
            + html1
            + "<h1>This step</h1>" + "<p>" + proofStep.getAppliedRuleApp().rule().displayName()
            + "</p>"
            // TODO: useful / useless / unknown
            + "<h1>Outputs</h1>"
            + html2
            + "<p>strikethrough label = useless node</p>";
        new HtmlDialog(parentWindow,
            "Dependency graph edge info", html, event -> {
                var parts = event.substring(1).split("_");
                var idx = Integer.parseInt(parts[1]);
                new ShowNodeInfoAction(mainWindow, tracker, graphNodes.get(idx))
                        .showDialog(parentWindow);
            });
    }
}
