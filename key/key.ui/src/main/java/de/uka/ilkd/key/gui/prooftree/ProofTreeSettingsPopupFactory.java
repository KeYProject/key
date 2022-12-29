package de.uka.ilkd.key.gui.prooftree;

import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.proof.Goal;

import javax.swing.*;
import javax.swing.tree.TreeNode;
import javax.swing.tree.TreePath;
import java.awt.event.ActionEvent;

import static de.uka.ilkd.key.gui.prooftree.ProofTreePopupFactory.ICON_SIZE;

public class ProofTreeSettingsPopupFactory {
    public static JPopupMenu create(ProofTreeView view, TreePath selectedPath) {
        final String menuName = "Choose Action";
        JPopupMenu menu = new JPopupMenu(menuName);
        ProofTreePopupFactory.ProofTreeContext context = ProofTreePopupFactory.createContext(view, selectedPath);

        menu.add(new Search(context));
        menu.addSeparator();

        menu.add(new ExpandAll(context));
        menu.add(new ExpandGoals(context));
        menu.add(new CollapseAll(context));
        menu.addSeparator();

        for (ProofTreeViewFilter filter : ProofTreeViewFilter.ALL) {
            FilterAction action = new FilterAction(context, filter);
            menu.add(new JCheckBoxMenuItem(action));
        }
        menu.addSeparator();

        menu.add(new JCheckBoxMenuItem(new TacletInfoToggle(context)));

        return menu;
    }

    static class ExpandAll extends ProofTreePopupFactory.ProofTreeAction {
        private static final long serialVersionUID = -8996407746579766286L;

        protected ExpandAll(ProofTreePopupFactory.ProofTreeContext context) {
            super(context);
            setName("Expand All");
            setIcon(IconFactory.plus(ICON_SIZE));
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            ProofTreeExpansionState.expandAll(context.delegateView);
        }
    }

    private static class FilterAction extends ProofTreePopupFactory.ProofTreeAction {
        private static final long serialVersionUID = -2972127068771960203L;
        private final ProofTreeViewFilter filter;

        public FilterAction(ProofTreePopupFactory.ProofTreeContext context, ProofTreeViewFilter filter) {
            super(context);
            this.filter = filter;
            setName(filter.name());
            setSelected(filter.isActive());
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            final boolean selected = isSelected();
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

    static class Search extends ProofTreePopupFactory.ProofTreeAction {
        private static final long serialVersionUID = -6543488911281521583L;

        public Search(ProofTreePopupFactory.ProofTreeContext context) {
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

    static class CollapseAll extends ProofTreePopupFactory.ProofTreeAction {
        private static final long serialVersionUID = 5343671322035834491L;

        public CollapseAll(ProofTreePopupFactory.ProofTreeContext context) {
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

    static class ExpandGoals extends ProofTreePopupFactory.ProofTreeAction {
        private static final long serialVersionUID = -8404655108317574685L;

        public ExpandGoals(ProofTreePopupFactory.ProofTreeContext context) {
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

    static class TacletInfoToggle extends ProofTreePopupFactory.ProofTreeAction {
        private static final long serialVersionUID = 1L;

        public TacletInfoToggle(ProofTreePopupFactory.ProofTreeContext context) {
            super(context);
            setName("Show taclet info (inner nodes only)");
            setSelected(context.window.isShowTacletInfo());
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            final boolean selected = isSelected();
            context.window.setShowTacletInfo(selected);
        }
    }
}
