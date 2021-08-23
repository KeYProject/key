package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofVisitor;
import de.uka.ilkd.key.rule.CloseByReferenceRule;
import de.uka.ilkd.key.rule.CloseByReferenceRule.CloseByReferenceRuleApp;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;

import javax.swing.*;
import java.util.*;

/**
 * This class is responsible for completing CloseByReferenceRuleApps. It shows a dialog with
 * potential partner nodes which could be used to close the selected goal. If no such potential
 * partners are present, this is indicated in the status line.
 *
 * @author Wolfram Pfeifer
 */
public final class CloseByReferenceCompletion implements InteractiveRuleApplicationCompletion {
    /** The single instance of this class. */
    public static final CloseByReferenceCompletion INSTANCE = new CloseByReferenceCompletion();

    private CloseByReferenceCompletion() {
    }

    @Override
    public IBuiltInRuleApp complete(IBuiltInRuleApp app, Goal goal, boolean forced) {
        CloseByReferenceRuleApp closeApp = (CloseByReferenceRuleApp) app;

        List<Node> potentialPartners = findPotentialPartners(goal);

        if (!potentialPartners.isEmpty()) {
            CloseByReferencePartnerSelectionDialog dialog =
                new CloseByReferencePartnerSelectionDialog(goal, potentialPartners);
            dialog.setVisible(true);
            Node chosen = dialog.getSelectedNode();
            if (chosen != null) {
                closeApp.setPartner(chosen);
                return closeApp;
            }
        } else {
            /* TODO: instead of making the rule always available from the context menu and showing
             *  this message when no potential partners are found, we could make it only available
             *  if there are possible partner nodes ... */
            JOptionPane.showMessageDialog(MainWindow.getInstance(),
                "<html>Closing by reference not possible: No potential partners found!<br>" +
                "Conditions for potential closing partners:<br>" +
                "<ul><li>partner node must be closed</li>" +
                "<li>sequent of the partner must be equal to the one the rule is applied to " +
                    "(modulo term labels and order of formulas)</li>" +
                "<li>all hidden formulas of the partner must also be available at the current " +
                    "goal </li></ul></html>", "Rule application not possible",
                JOptionPane.INFORMATION_MESSAGE);
        }
        return null;
    }

    /**
     * Finds all potential partner nodes which could be used to close the given goal.
     * @param goal the goal to search partners for
     * @return all potential partner nodes (could be empty)
     */
    private static List<Node> findPotentialPartners(Goal goal) {
        List<Node> potentialPartners = new ArrayList<>();
        goal.proof().accept(new ProofVisitor() {
            @Override
            public void visit(Proof proof, Node visitedNode) {
                if (visitedNode.isClosed()
                    && goal.sequent().equalsModIrrelevantTermLabels(visitedNode.sequent())
                    && CloseByReferenceRule.localRulesAreCompatible(goal, visitedNode)) {
                    potentialPartners.add(visitedNode);
                    // already found one, do not visit this subtree further
                    return;
                }

                // visit children
                for (Iterator<Node> it = visitedNode.childrenIterator(); it.hasNext(); ) {
                    Node n = it.next();
                    visit(proof, n);
                }
            }
        });
        return potentialPartners;
    }

    @Override
    public boolean canComplete(IBuiltInRuleApp app) {
        return app instanceof CloseByReferenceRuleApp;
    }
}
