/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.prooftree;

import java.awt.event.ActionEvent;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.function.Predicate;
import javax.swing.*;
import javax.swing.tree.TreeNode;
import javax.swing.tree.TreePath;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.InspectorForDecisionPredicates;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.ProofMacroMenu;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.actions.ShowProofStatistics;
import de.uka.ilkd.key.gui.actions.useractions.RunStrategyOnNodeUserAction;
import de.uka.ilkd.key.gui.extension.api.DefaultContextMenuKind;
import de.uka.ilkd.key.gui.extension.impl.KeYGuiExtensionFacade;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.nodeviews.SequentViewDock;
import de.uka.ilkd.key.gui.notification.events.ExceptionFailureEvent;
import de.uka.ilkd.key.gui.notification.events.GeneralInformationEvent;
import de.uka.ilkd.key.gui.utilities.CheckedUserInput;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.delayedcut.DelayedCutListener;
import de.uka.ilkd.key.proof.delayedcut.DelayedCutProcessor;
import de.uka.ilkd.key.prover.impl.DefaultTaskStartedInfo;
import de.uka.ilkd.key.rule.OneStepSimplifierRuleApp;
import de.uka.ilkd.key.settings.FeatureSettings;
import de.uka.ilkd.key.settings.GeneralSettings;

import org.key_project.prover.engine.TaskStartedInfo;

import static de.uka.ilkd.key.settings.FeatureSettings.createFeature;

/**
 * Factory for popup menus on proof nodes in the {@link ProofTreeView}.
 */
public final class ProofTreePopupFactory {
    public static final int ICON_SIZE = 16;
    public static final FeatureSettings.Feature FEATURE_DELAY_CUT =
        createFeature("DELAY_CUT", "Activates the delayed cut rule.");

    private ProofTreePopupFactory() {
    }

    /**
     * A filter that returns true iff the given TreePath denotes a One-Step-Simplifier-Node.
     */
    public static boolean ossPathFilter(TreePath tp) {
        // filter out nodes with only OSS children (i.e., OSS nodes are not expanded)
        // (take care to not filter out any GUIBranchNodes accidentally!)
        Object o = tp.getLastPathComponent();
        if (o instanceof GUIProofTreeNode n) {
            return !(n.getNode().getAppliedRuleApp() instanceof OneStepSimplifierRuleApp);
        }
        return true;
    }

    /**
     * A predicate that filters oss nodes if filterOss is true
     */
    public static Predicate<TreePath> ossPathFilter(boolean filterOss) {
        return filterOss ? n -> true : ProofTreePopupFactory::ossPathFilter;
    }

    public static ProofTreeContext createContext(ProofTreeView view, TreePath selectedPath) {
        ProofTreeContext context = new ProofTreeContext();
        context.proofTreeView = view;
        context.path = selectedPath;
        if (selectedPath.getLastPathComponent() instanceof GUIProofTreeNode) {
            context.branch = selectedPath.getParentPath();
            context.invokedNode =
                ((GUIProofTreeNode) selectedPath.getLastPathComponent()).getNode();
        } else {
            context.branch = selectedPath;
            context.invokedNode = ((GUIBranchNode) selectedPath.getLastPathComponent()).getNode();
        }

        context.delegateModel = view.getDelegateModel();
        context.delegateView = view.delegateView;
        context.window = MainWindow.getInstance();
        context.mediator = context.window.getMediator();
        context.proof = context.mediator.getSelectedProof();
        return context;
    }

    private static void initMacroMenu(JPopupMenu menu, ProofTreeContext ctx) {
        ProofMacroMenu macroMenu = new ProofMacroMenu(ctx.mediator, null);
        if (!macroMenu.isEmpty()) {
            menu.add(macroMenu);
        }
    }

    private static void initMenu(JPopupMenu menu, ProofTreeContext ctx) {
        menu.add(new RunStrategyOnNode(ctx));
        menu.add(new Prune(ctx));

        initMacroMenu(menu, ctx);


        final var delayedCut = new DelayedCut(ctx);
        if (FeatureSettings.isFeatureActivated(FEATURE_DELAY_CUT)) {
            menu.add(delayedCut);
        }



        menu.addSeparator();

        menu.add(new Notes(ctx));

        menu.addSeparator();

        menu.add(new ExpandAllBelow(ctx));
        menu.add(new ExpandGoalsBelow(ctx));
        menu.add(new CollapseBelow(ctx));
        menu.add(new CollapseOtherBranches(ctx));

        menu.addSeparator();

        menu.add(new PrevSibling(ctx));
        menu.add(new NextSibling(ctx));

        menu.addSeparator();

        menu.add(new SetGoalsBelowEnableStatus(ctx, false));
        menu.add(new SetGoalsBelowEnableStatus(ctx, true));

        menu.addSeparator();

        menu.add(new SubtreeStatistics(ctx));
        menu.add(new SequentViewDock.OpenCurrentNodeAction(ctx.window, ctx.invokedNode));
    }

    public static JPopupMenu create(ProofTreeView view, TreePath selectedPath) {
        final String menuName = "Choose Action";
        JPopupMenu menu = new JPopupMenu(menuName);
        ProofTreeContext context = createContext(view, selectedPath);
        initMenu(menu, context);

        menu.addSeparator();
        KeYGuiExtensionFacade.addContextMenuItems(DefaultContextMenuKind.PROOF_TREE, menu,
            context.invokedNode, context.mediator);

        if (menu.getComponent(menu.getComponentCount() - 1) instanceof JPopupMenu.Separator) {
            menu.remove(menu.getComponentCount() - 1);
        }

        return menu;
    }

    /*
     * private void expandGoalsBelow() { Object tmpNode = branch.getLastPathComponent(); if (branch
     * == path) { ExpansionState.collapseAll(delegateView, branch); } else { for (int count =
     * delegateModel.getChildCount(tmpNode), i = 0; i < count; i++) { Object child =
     * delegateModel.getChild(tmpNode, i); if (!delegateModel.isLeaf(child))
     * ExpansionState.collapseAll(delegateView, branch .pathByAddingChild(child)); } }
     * Iterator<Goal> it = proof.openGoals().iterator(); Node n; while (it.hasNext()) { n =
     * it.next().node(); GUIAbstractTreeNode node = delegateModel.getProofTreeNode(n); if (node ==
     * null) break; TreeNode[] obs = node.getPath(); TreePath tp = new TreePath(obs); if
     * (branch.isDescendant(tp)) { delegateView.makeVisible(tp); } } }
     */

    public static class ProofTreeContext {
        GUIProofTreeModel delegateModel;
        ProofTreeView proofTreeView;
        MainWindow window;
        Proof proof;
        KeYMediator mediator;
        Node invokedNode;
        TreePath path, branch;
        JTree delegateView;
    }

    static class SubtreeStatistics extends ProofTreeAction {
        private static final long serialVersionUID = -8452239418108180349L;

        protected SubtreeStatistics(ProofTreeContext context) {
            super(context);
            setName("Show Subtree Statistics");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            final Proof proof = context.proof;
            if (proof == null) {
                MainWindow.getInstance()
                        .notify(new GeneralInformationEvent("No statistics available.",
                            "If you wish to see the statistics "
                                + "for a proof you have to load one first"));
            } else {
                new ShowProofStatistics.Window(MainWindow.getInstance(), context.invokedNode)
                        .setVisible(true);
            }
        }
    }

    static class CollapseOtherBranches extends ProofTreeAction {
        private static final long serialVersionUID = -6461403850298323327L;

        protected CollapseOtherBranches(ProofTreeContext context) {
            super(context);
            setName("Collapse Other Branches");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            context.proofTreeView.collapseOthers(context.branch);
        }
    }

    static class ExpandGoalsBelow extends ProofTreeAction {
        private static final long serialVersionUID = -500754845710844009L;

        protected ExpandGoalsBelow(ProofTreeContext context) {
            super(context);
            setName("Expand Goals Only Below");
            setIcon(IconFactory.expandGoals(ICON_SIZE));
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            // collapse all below
            ProofTreeExpansionState.collapseAllBelow(context.delegateView, context.branch);

            // expand goals below
            Iterator<Goal> it = context.proof.openGoals().iterator();
            Node n;
            while (it.hasNext()) {
                n = it.next().node();
                GUIAbstractTreeNode node = context.delegateModel.getProofTreeNode(n);
                if (node == null) {
                    break;
                }
                TreeNode[] obs = node.getPath();
                TreePath tp = new TreePath(obs);
                if (context.branch.isDescendant(tp)) {
                    context.delegateView.makeVisible(tp);
                }
            }

        }
    }

    static class ExpandAllBelow extends ProofTreeAction {
        private static final long serialVersionUID = 850060084128297700L;

        public ExpandAllBelow(ProofTreeContext context) {
            super(context);
            setName("Expand All Below");
            setIcon(IconFactory.plus(ICON_SIZE));
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            // expands everything below the given path except for OSS nodes
            ProofTreeExpansionState.expandAllBelow(context.delegateView, context.path,
                ossPathFilter(context.proofTreeView.isExpandOSSNodes()));
        }
    }

    static class CollapseBelow extends ProofTreeAction {
        private static final long serialVersionUID = -7283113335781286556L;

        public CollapseBelow(ProofTreeContext context) {
            super(context);
            setName("Collapse Below");
            setIcon(IconFactory.minus(ICON_SIZE));
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            ProofTreeExpansionState.collapseAllBelow(context.delegateView, context.path);
        }
    }

    static class PrevSibling extends ProofTreeAction {
        private static final long serialVersionUID = 8705344500396898345L;

        public PrevSibling(ProofTreeContext context) {
            super(context);
            setName("Previous Sibling");
            setIcon(IconFactory.previous(ICON_SIZE));
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            Object node = context.branch.getLastPathComponent();
            TreeNode parent = ((GUIAbstractTreeNode) node).getParent();
            if (parent == null) {
                return;
            }
            Object sibling = context.delegateModel.getChild(parent,
                context.delegateModel.getIndexOfChild(parent, node) - 1);
            if (!(sibling instanceof GUIBranchNode)) {
                int index = context.delegateModel.getIndexOfChild(parent, node);
                for (int i = parent.getChildCount(); i > index; i--) {
                    sibling = context.delegateModel.getChild(parent, i);
                    if (sibling instanceof GUIBranchNode) {
                        break;
                    }
                }
            }
            if (sibling instanceof GUIBranchNode) {
                var tp = context.proofTreeView.selectBranchNode((GUIBranchNode) sibling);
                if (tp != null) {
                    context.delegateView.setSelectionPath(tp);
                    context.delegateView.scrollPathToVisible(tp);
                }
            }
        }
    }

    static class NextSibling extends ProofTreeAction {
        private static final long serialVersionUID = 2337297147243419973L;

        public NextSibling(ProofTreeContext context) {
            super(context);
            setName("Next Sibling");
            setIcon(IconFactory.next(ICON_SIZE));
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            Object node = context.branch.getLastPathComponent();
            TreeNode parent = ((GUIAbstractTreeNode) node).getParent();
            if (parent == null) {
                return;
            }
            Object sibling = context.delegateModel.getChild(parent,
                context.delegateModel.getIndexOfChild(parent, node) + 1);
            if (!(sibling instanceof GUIBranchNode)) {
                int index = context.delegateModel.getIndexOfChild(parent, node);
                for (int i = 0; i < index; i++) {
                    sibling = context.delegateModel.getChild(parent, i);
                    if (sibling instanceof GUIBranchNode) {
                        break;
                    }
                }
            }
            if (sibling instanceof GUIBranchNode) {
                var tp = context.proofTreeView.selectBranchNode((GUIBranchNode) sibling);
                if (tp != null) {
                    context.delegateView.setSelectionPath(tp);
                    context.delegateView.scrollPathToVisible(tp);
                }
            }
        }
    }

    static class Notes extends ProofTreeAction {
        private static final long serialVersionUID = -6871120844080468856L;

        public Notes(ProofTreeContext context) {
            super(context);
            setName("Edit Notes...");
            setIcon(IconFactory.editFile(ICON_SIZE));
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            // display a dialog to attach text to the node
            final Icon editIcon = IconFactory.editFile(20);
            final String origNotes = context.invokedNode.getNodeInfo().getNotes();
            final String newNotes = (String) JOptionPane.showInputDialog(context.proofTreeView,
                null, "Annotate this proof node", JOptionPane.PLAIN_MESSAGE, editIcon, null,
                origNotes);
            if (newNotes != null) {
                if (newNotes.length() == 0) {
                    context.invokedNode.getNodeInfo().setNotes(null);
                } else {
                    context.invokedNode.getNodeInfo().setNotes(newNotes);
                }
            }
        }
    }

    static class Prune extends ProofTreeAction {
        private static final long serialVersionUID = -1744963704210861370L;

        public Prune(ProofTreeContext context) {
            super(context);
            setName("Prune Proof");
            setIcon(IconFactory.pruneLogo(ICON_SIZE));
            setEnabled(false);
            if (context.proof != null) {
                // disable pruning for goals and disable it for closed subtrees if the command line
                // option "--no-pruning-closed" is set (saves memory)
                if (!context.proof.isOpenGoal(context.invokedNode)
                        && !context.proof.isClosedGoal(context.invokedNode)
                        && (context.proof.getSubtreeGoals(context.invokedNode).size() > 0
                                || (!GeneralSettings.noPruningClosed && context.proof
                                        .getClosedSubtreeGoals(context.invokedNode).size() > 0))) {
                    setEnabled(true);
                }
            }
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            context.delegateModel.setAttentive(false);
            context.mediator.setBack(context.invokedNode);
            context.delegateModel.updateTree(null);
            context.delegateModel.setAttentive(true);
            context.proofTreeView.makeNodeVisible(context.invokedNode);
        }
    }

    static class DelayedCut extends ProofTreeAction {
        private static final long serialVersionUID = 2264044175802298829L;

        public DelayedCut(ProofTreeContext context) {
            super(context);
            setName("Delayed Cut");
            setEnabled(false);
            if (context.proof != null) {
                if (!context.invokedNode.leaf()
                        && context.proof.getSubtreeGoals(context.invokedNode).size() > 0) {
                    setEnabled(true);
                }
            }
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            context.delegateModel.setAttentive(false);
            if (processDelayedCut(context.invokedNode)) {
                context.delegateModel.updateTree(null);
            }
            context.delegateModel.setAttentive(true);
            context.proofTreeView.makeNodeVisible(context.mediator.getSelectedNode());
        }

        public boolean processDelayedCut(final Node invokedNode) {
            KeYMediator mediator = context.mediator;
            if (mediator.ensureProofLoaded()) {
                final Proof proof = mediator.getSelectedProof();
                final String result =
                    CheckedUserInput.showAsDialog("Cut Formula", "Please supply a formula:", null,
                        "",
                        new InspectorForDecisionPredicates(proof.getServices(),
                            invokedNode,
                            de.uka.ilkd.key.proof.delayedcut.DelayedCut.DECISION_PREDICATE_IN_ANTECEDENT,
                            DelayedCutProcessor.getApplicationChecks()),
                        true);

                if (result == null) {
                    return false;
                }

                JTerm formula =
                    InspectorForDecisionPredicates.translate(proof.getServices(), result);

                DelayedCutProcessor processor = new DelayedCutProcessor(proof, invokedNode,
                    formula,
                    de.uka.ilkd.key.proof.delayedcut.DelayedCut.DECISION_PREDICATE_IN_ANTECEDENT);
                processor.add(new DelayedCutListener() {

                    @Override
                    public void eventRebuildingTree(final int currentTacletNumber,
                            final int totalNumber) {

                        SwingUtilities.invokeLater(() -> {
                            mediator.getUI().taskStarted(
                                new DefaultTaskStartedInfo(TaskStartedInfo.TaskKind.Other,
                                    "Rebuilding...", totalNumber));
                            mediator.getUI().taskProgress(currentTacletNumber);

                        });
                    }

                    @Override
                    public void eventEnd(
                            de.uka.ilkd.key.proof.delayedcut.DelayedCut cutInformation) {
                        SwingUtilities.invokeLater(new Runnable() {

                            @Override
                            public void run() {
                                mediator.getUI().resetStatus(this);
                                mediator.startInterface(true);
                            }
                        });

                    }

                    @Override
                    public void eventCutting() {
                        SwingUtilities.invokeLater(() -> mediator.getUI().taskStarted(
                            new DefaultTaskStartedInfo(TaskStartedInfo.TaskKind.Other, "Cutting...",
                                0)));

                    }

                    @Override
                    public void eventException(Throwable throwable) {
                        mediator.startInterface(true);

                        mediator.notify(new ExceptionFailureEvent(
                            "The cut could" + "not be processed successfully. In order to "
                                + "preserve consistency the proof is pruned."
                                + " For more information see details or output of your console.",
                            throwable));

                        SwingUtilities
                                .invokeLater(() -> proof.pruneProof(invokedNode));
                    }
                });
                mediator.stopInterface(true);

                Thread thread = new Thread(processor, "DelayedCutListener");
                thread.start();
            }
            return true;

        }
    }



    static class RunStrategyOnNode extends ProofTreeAction {
        private static final long serialVersionUID = -7028621462695539683L;

        protected RunStrategyOnNode(ProofTreeContext context) {
            super(context);
            setName("Apply Strategy");
            setIcon(IconFactory.strategyStartLogo(ICON_SIZE));
            setEnabled(context.proof != null);
        }

        /**
         * run automatic on the currently selected node. All enabled goals below the current node
         * are taken into consideration.
         * <p>
         * CAUTION: If the node itself is a goal then allow applying rules to it even if it were
         * disabled. Desired behavior?
         */
        @Override
        public void actionPerformed(ActionEvent e) {
            new RunStrategyOnNodeUserAction(context.mediator, context.proof, context.invokedNode)
                    .actionPerformed(e);
        }
    }

    /**
     * Action for enabling/disabling all goals below "node".
     *
     * @author mulbrich
     */
    private static final class SetGoalsBelowEnableStatus extends DisableGoal {
        private static final long serialVersionUID = -2150188528163599512L;
        private final ProofTreeContext context;

        public SetGoalsBelowEnableStatus(ProofTreeContext ctx, boolean enableGoals) {
            context = ctx;
            this.enableGoals = enableGoals;

            String action = enableGoals ? "Automatic" : "Interactive";
            putValue(NAME, "Set All Goals Below to " + action);
            if (enableGoals) {
                putValue(SHORT_DESCRIPTION, "Include this node and all goals "
                    + "in the subtree in automatic rule application");
                putValue(SMALL_ICON, KEY_HOLE_PULL_DOWN_MENU);
            } else {
                putValue(SHORT_DESCRIPTION, "Exclude this node and all goals "
                    + "in the subtree from automatic rule application");
                putValue(SMALL_ICON, KEY_HOLE_DISABLED_PULL_DOWN_MENU);
            }
        }

        /*
         * return all subgoals of the current node.
         */
        @Override
        public Iterable<Goal> getGoalList() {
            return context.proof.getSubtreeGoals(context.invokedNode);
        }

        /**
         * In addition to marking setting goals, update the tree model so that the label sizes are
         * recalculated
         */
        @Override
        public void actionPerformed(ActionEvent e) {
            var selectedNode = context.proofTreeView.getSelectedNode();
            context.delegateModel.setBatchGoalStateChange(true, null);
            super.actionPerformed(e);
            List<Node> goals = new ArrayList<>();
            getGoalList().forEach(x -> goals.add(x.node()));
            context.delegateModel.setBatchGoalStateChange(false, goals);
            // make sure the node is selected again
            if (selectedNode != null) {
                context.proofTreeView.makeNodeVisible(selectedNode);
            }
            // repainting the tree after the completion of this event is done automatically
        }
    }

    public static abstract class ProofTreeAction extends KeyAction {
        private static final long serialVersionUID = 2686349019163064481L;
        protected final ProofTreeContext context;

        protected ProofTreeAction(ProofTreeContext context) {
            this.context = context;
        }
    }
}
