package de.uka.ilkd.key.gui.prooftree;

import java.awt.Component;
import java.awt.event.ActionEvent;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.function.Function;

import javax.swing.Action;
import javax.swing.Icon;
import javax.swing.JCheckBoxMenuItem;
import javax.swing.JMenuItem;
import javax.swing.JOptionPane;
import javax.swing.JPopupMenu;
import javax.swing.JSeparator;
import javax.swing.JTree;
import javax.swing.tree.TreeNode;
import javax.swing.tree.TreePath;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.Main;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.ProofMacroMenu;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.extension.api.DefaultContextMenuKind;
import de.uka.ilkd.key.gui.extension.impl.KeYGuiExtensionFacade;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.nodeviews.SequentViewDock;
import de.uka.ilkd.key.gui.notification.events.GeneralInformationEvent;
import de.uka.ilkd.key.gui.proofdiff.ProofDifferenceView;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.util.Pair;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

public class ProofTreePopupFactory {
    public static final int ICON_SIZE = 16;
    private List<Function<ProofTreeContext, Component>> builders =
        new ArrayList<Function<ProofTreeContext, Component>>();

    protected ProofTreePopupFactory() {
        addAction(RunStrategyOnNode::new);
        addAction(Prune::new);
        add(this::getMacroMenu);

        if (Main.isExperimentalMode()) {
            addAction(DelayedCut::new);
        }

        addSeparator();
        addAction(Notes::new);
        addSeparator();
        addAction(ExpandAll::new);
        addAction(ExpandAllBelow::new);
        addAction(ExpandGoals::new);
        addAction(ExpandGoalsBelow::new);
        addAction(CollapseAll::new);
        addAction(CollapseOtherBranches::new);
        addAction(CollapseBelow::new);
        addSeparator();
        addAction(PrevSibling::new);
        addAction(NextSibling::new);

        addSeparator();

        for (ProofTreeViewFilter filter : ProofTreeViewFilter.ALL) {
            add(ctx -> {
                FilterAction action = new FilterAction(ctx, filter);
                // JRadioButtonMenuItem item = new JRadioButtonMenuItem(action);
                return new JCheckBoxMenuItem(action);
            });
        }

        addAction(Search::new);
        addSeparator();
        addAction(ctx -> new SetGoalsBelowEnableStatus(ctx, false));
        addAction(ctx -> new SetGoalsBelowEnableStatus(ctx, true));

        addSeparator();
        addAction(SubtreeStatistics::new);

        addAction(ctx -> new SequentViewDock.OpenCurrentNodeAction(ctx.window, ctx.invokedNode));
        addAction(
            ctx -> new ProofDifferenceView.OpenDifferenceWithParent(ctx.window, ctx.invokedNode));
    }

    private Component getMacroMenu(ProofTreeContext proofTreeContext) {
        ProofMacroMenu macroMenu = new ProofMacroMenu(proofTreeContext.mediator, null);
        if (!macroMenu.isEmpty()) {
            return macroMenu;
        }
        return null;
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

        context.delegateModel = view.delegateModel;
        context.delegateView = view.delegateView;
        context.window = MainWindow.getInstance();
        context.mediator = context.window.getMediator();
        context.proof = context.mediator.getSelectedProof();
        return context;
    }

    private void addSeparator() {
        add(ctx -> new JSeparator());
    }

    public void add(Function<ProofTreeContext, Component> act) {
        builders.add(act);
    }

    public void addAction(Function<ProofTreeContext, Action> act) {
        add(ctx -> new JMenuItem(act.apply(ctx)));
    }

    public JPopupMenu create(ProofTreeView view, TreePath selectedPath) {
        final String menuName = "Choose Action";
        JPopupMenu menu = new JPopupMenu(menuName);
        ProofTreeContext context = createContext(view, selectedPath);
        builders.forEach(it -> {
            Component entry = it.apply(context);
            if (entry != null) {
                menu.add(entry);
            }
        });

        menu.addSeparator();
        KeYGuiExtensionFacade.addContextMenuItems(DefaultContextMenuKind.PROOF_TREE, menu,
            context.invokedNode, context.mediator);

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

    private static class ProofTreeContext {
        GUIProofTreeModel delegateModel;
        ProofTreeView proofTreeView;
        MainWindow window;
        Proof proof;
        KeYMediator mediator;
        Node invokedNode;
        TreePath path, branch;
        JTree delegateView;
    }

    class SubtreeStatistics extends ProofTreeAction {
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
                int openGoals = 0;

                Iterator<Node> leavesIt = context.invokedNode.leavesIterator();
                while (leavesIt.hasNext()) {
                    if (proof.getGoal(leavesIt.next()) != null) {
                        openGoals++;
                    }
                }

                String stats;
                if (openGoals > 0) {
                    stats = openGoals + " open goal" + (openGoals > 1 ? "s." : ".");
                } else {
                    stats = "Closed.";
                }
                stats += "\n\n";

                for (Pair<String, String> x : context.invokedNode.statistics().getSummary()) {
                    if ("".equals(x.second)) {
                        stats += "\n";
                    }
                    stats += x.first + ": " + x.second + "\n";
                }

                JOptionPane.showMessageDialog(MainWindow.getInstance(), stats, "Proof Statistics",
                    JOptionPane.INFORMATION_MESSAGE);
            }
        }
    }

    class CollapseOtherBranches extends ProofTreeAction {
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

    class ExpandGoalsBelow extends ProofTreeAction {
        private static final long serialVersionUID = -500754845710844009L;

        protected ExpandGoalsBelow(ProofTreeContext context) {
            super(context);
            setName("Expand Goals Only Below");
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

    class ExpandAll extends ProofTreeAction {
        private static final long serialVersionUID = -8996407746579766286L;

        protected ExpandAll(ProofTreeContext context) {
            super(context);
            setName("Expand All");
            setIcon(IconFactory.plus(ICON_SIZE));
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            ProofTreeExpansionState.expandAll(context.delegateView);

        }
    }

    class ExpandAllBelow extends ProofTreeAction {
        private static final long serialVersionUID = 850060084128297700L;

        public ExpandAllBelow(ProofTreeContext context) {
            super(context);

            setName("Expand All Below");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            ProofTreeExpansionState.expandAllBelow(context.delegateView, context.path);
        }
    }

    class ExpandGoals extends ProofTreeAction {
        private static final long serialVersionUID = -8404655108317574685L;

        public ExpandGoals(ProofTreeContext context) {
            super(context);
            setName("Expand Goals Only");
            setIcon(IconFactory.expandGoals(ICON_SIZE));
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            for (final Goal g : context.proof.openGoals()) {
                context.proofTreeView.makeNodeExpanded(g.node());
            }
            context.proofTreeView.collapseClosedNodes();
            // do not show selected node if it is not on the path to an
            // open goal, but do expand root
            // makeNodeVisible(mediator.getSelectedNode());
            context.delegateView.expandRow(0);
        }
    }

    class CollapseAll extends ProofTreeAction {
        private static final long serialVersionUID = 5343671322035834491L;

        public CollapseAll(ProofTreeContext context) {
            super(context);
            setName("Collapse All");
            setIcon(IconFactory.minus(ICON_SIZE));
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            ProofTreeExpansionState.collapseAll(context.delegateView);
            context.delegateView.expandRow(0);
        }
    }

    class CollapseBelow extends ProofTreeAction {
        private static final long serialVersionUID = -7283113335781286556L;

        public CollapseBelow(ProofTreeContext context) {
            super(context);
            setName("Collapse Below");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            ProofTreeExpansionState.collapseAllBelow(context.delegateView, context.path);
        }
    }

    class PrevSibling extends ProofTreeAction {
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
            if (!(sibling != null && sibling instanceof GUIBranchNode)) {
                int index = context.delegateModel.getIndexOfChild(parent, node);
                for (int i = parent.getChildCount(); i > index; i--) {
                    sibling = context.delegateModel.getChild(parent, i);
                    if (sibling != null && sibling instanceof GUIBranchNode) {
                        break;
                    }
                }
            }
            if (sibling != null && sibling instanceof GUIBranchNode) {
                context.proofTreeView.selectBranchNode((GUIBranchNode) sibling);
            }
        }
    }

    class NextSibling extends ProofTreeAction {
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
            if (!(sibling != null && sibling instanceof GUIBranchNode)) {
                int index = context.delegateModel.getIndexOfChild(parent, node);
                for (int i = 0; i < index; i++) {
                    sibling = context.delegateModel.getChild(parent, i);
                    if (sibling != null && sibling instanceof GUIBranchNode) {
                        break;
                    }
                }
            }
            if (sibling != null && sibling instanceof GUIBranchNode) {
                context.proofTreeView.selectBranchNode((GUIBranchNode) sibling);
            }
        }
    }

    class Notes extends ProofTreeAction {
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

    class Search extends ProofTreeAction {
        private static final long serialVersionUID = -6543488911281521583L;

        public Search(ProofTreeContext context) {
            super(context);
            setName("Search");
            setIcon(IconFactory.search2(ICON_SIZE));
            setAcceleratorKey(de.uka.ilkd.key.gui.prooftree.ProofTreeView.searchKeyStroke);
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            context.proofTreeView.showSearchPanel();
        }
    }

    class Prune extends ProofTreeAction {
        private static final long serialVersionUID = -1744963704210861370L;

        public Prune(ProofTreeContext context) {
            super(context);
            setName("Prune Proof");
            setIcon(IconFactory.pruneLogo(ICON_SIZE));
            setEnabled(false);
            if (context.proof != null) {
                // disable pruning for goals and disable it for closed subtrees if the command line
                // option "--no-pruning-closed" is set (saves memory)
                if (!context.proof.isGoal(context.invokedNode)
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

    class DelayedCut extends ProofTreeAction {
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
            if (context.mediator.processDelayedCut(context.invokedNode)) {
                context.delegateModel.updateTree(null);
            }
            context.delegateModel.setAttentive(true);
            context.proofTreeView.makeNodeVisible(context.mediator.getSelectedNode());
        }
    }

    class RunStrategyOnNode extends ProofTreeAction {
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
            Goal invokedGoal = context.proof.getGoal(context.invokedNode);
            KeYMediator r = context.mediator;
            // is the node a goal?
            if (invokedGoal == null) {
                ImmutableList<Goal> enabledGoals =
                    context.proof.getSubtreeEnabledGoals(context.invokedNode);
                // This method delegates the request only to the UserInterfaceControl
                // which implements the functionality.
                // No functionality is allowed in this method body!
                r.getUI().getProofControl().startAutoMode(r.getSelectedProof(), enabledGoals);
            } else {
                // This method delegates the request only to the UserInterfaceControl
                // which implements the functionality.
                // No functionality is allowed in this method body!
                r.getUI().getProofControl().startAutoMode(r.getSelectedProof(),
                    ImmutableSLList.<Goal>nil().prepend(invokedGoal));
            }
        }
    }

    /**
     * Action for enabling/disabling all goals below "node".
     *
     * @author mulbrich
     */
    private final class SetGoalsBelowEnableStatus extends DisableGoal {
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

        /*
         * In addition to marking setting goals, update the tree model so that the label sizes are
         * recalculated
         */
        @Override
        public void actionPerformed(ActionEvent e) {
            context.delegateModel.setBatchGoalStateChange(true);
            super.actionPerformed(e);
            context.delegateModel.setBatchGoalStateChange(false);
            // trigger repainting the tree after the completion of this event.
            context.delegateView.repaint();
        }
    }

    public abstract class ProofTreeAction extends KeyAction {
        private static final long serialVersionUID = 2686349019163064481L;
        protected final ProofTreeContext context;

        protected ProofTreeAction(ProofTreeContext context) {
            this.context = context;
        }
    }

    private class FilterAction extends ProofTreeAction {
        private static final long serialVersionUID = -2972127068771960203L;
        private final ProofTreeViewFilter filter;

        public FilterAction(ProofTreeContext context, ProofTreeViewFilter filter) {
            super(context);
            this.filter = filter;
            setName(filter.name());
            setSelected(filter.isActive());
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            final boolean selected = isSelected();
            final Object source = e.getSource();
            if (!filter.global()) {
                context.delegateModel.setFilter(filter, selected);
                if (context.branch == context.path) {
                    if (context.delegateModel.getRoot() instanceof GUIBranchNode) {
                        TreeNode node = ((GUIAbstractTreeNode) context.delegateModel.getRoot())
                                .findBranch(context.invokedNode);
                        if (node instanceof GUIBranchNode) {
                            context.proofTreeView.selectBranchNode((GUIBranchNode) node);
                        }
                    }
                } else {
                    context.delegateView.scrollPathToVisible(context.path);
                    context.delegateView.setSelectionPath(context.path);
                }
            } else {
                context.delegateModel.setFilter(filter, selected);
                if (context.branch == context.path) {
                    if (/* e.getStateChange() != ItemEvent.SELECTED */ !selected) {
                        if (context.delegateModel.getRoot() instanceof GUIBranchNode) {
                            TreeNode node = ((GUIAbstractTreeNode) context.delegateModel.getRoot())
                                    .findBranch(context.invokedNode);
                            if (node instanceof GUIBranchNode) {
                                context.proofTreeView.selectBranchNode((GUIBranchNode) node);
                            }
                        }
                    } else {
                        if (context.invokedNode.parent() == null || context.delegateModel
                                .getProofTreeNode(context.invokedNode.parent())
                                .findChild(context.invokedNode.parent()) == null) {
                            // it's still a branch
                            if (context.delegateModel.getRoot() instanceof GUIBranchNode) {
                                TreeNode node =
                                    ((GUIAbstractTreeNode) context.delegateModel.getRoot())
                                            .findBranch(context.invokedNode);
                                if (node instanceof GUIBranchNode) {
                                    context.proofTreeView.selectBranchNode((GUIBranchNode) node);
                                }
                            }
                        } else {
                            TreePath tp = new TreePath(context.delegateModel
                                    .getProofTreeNode(context.invokedNode).getPath());
                            context.delegateView.scrollPathToVisible(tp);
                            context.delegateView.setSelectionPath(tp);
                        }
                    }
                } else {
                    TreePath tp = new TreePath(
                        context.delegateModel.getProofTreeNode(context.invokedNode).getPath());
                    context.delegateView.scrollPathToVisible(tp);
                    context.delegateView.setSelectionPath(tp);
                }
            }
        }
    }
}
