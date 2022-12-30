package de.uka.ilkd.key.gui.prooftree;

import bibliothek.gui.dock.common.action.CMenu;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.docking.DockingHelper;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import javax.swing.*;
import javax.swing.tree.TreeNode;
import javax.swing.tree.TreePath;
import java.awt.event.ActionEvent;

import static de.uka.ilkd.key.gui.prooftree.ProofTreePopupFactory.ICON_SIZE;

public class ProofTreeSettingsMenuFactory {
    public static CMenu create(ProofTreeView view) {
        // TODO: action is used only to extract the properties from it
        // TODO: our classes (DockingHelper) can currently not really handle CMenu
        TreeSettingsAction action = new TreeSettingsAction();
        CMenu menu = new CMenu((String) action.getValue(Action.NAME),
                (Icon) action.getValue(Action.SMALL_ICON));
        DockingHelper.deriveBaseProperties(menu, action);

        menu.add(DockingHelper.translateAction(new ProofTreeSettingsMenuFactory.Search(view)));
        menu.addSeparator();

        menu.add(DockingHelper.translateAction(new ProofTreeSettingsMenuFactory.ExpandAll(view)));
        menu.add(DockingHelper.translateAction(new ProofTreeSettingsMenuFactory.ExpandGoals(view)));
        menu.add(DockingHelper.translateAction(new ProofTreeSettingsMenuFactory.CollapseAll(view)));
        menu.addSeparator();

        /*for (ProofTreeViewFilter filter : ProofTreeViewFilter.ALL) {
            ProofTreeSettingsMenuFactory.FilterAction
                filterAction = new ProofTreeSettingsMenuFactory.FilterAction(view, filter);
            menu.add(DockingHelper.translateAction(filterAction));
        }*/
        menu.addSeparator();

        menu.add(DockingHelper.translateAction(new ProofTreeSettingsMenuFactory.TacletInfoToggle(view)));
        return menu;
    }

    static class ExpandAll extends ProofTreeSettings {

        protected ExpandAll(ProofTreeView view) {
            super(view);
            setName("Expand All");
            setIcon(IconFactory.plus(ICON_SIZE));
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            //mediator.getSelectedProof().
            ProofTreeExpansionState.expandAll(view.delegateView);
        }
    }

    protected static class FilterAction extends ProofTreeSettings {
        private static final long serialVersionUID = -2972127068771960203L;
        private final ProofTreeViewFilter filter;

        public FilterAction(ProofTreeView view, ProofTreeViewFilter filter) {
            super(view);
            this.filter = filter;
            setName(filter.name());
            setSelected(filter.isActive());
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            final boolean selected = isSelected();

            final TreePath selectedPath = view.delegateModel.getSelection();
            final TreePath branch;
            final Node invokedNode;
            if (selectedPath.getLastPathComponent() instanceof GUIProofTreeNode) {
                branch = selectedPath.getParentPath();
                invokedNode =
                        ((GUIProofTreeNode) selectedPath.getLastPathComponent()).getNode();
            } else {
                branch = selectedPath;
                invokedNode = ((GUIBranchNode) selectedPath.getLastPathComponent()).getNode();
            }

            if (!filter.global()) {
                view.delegateModel.setFilter(filter, selected);
                if (branch == selectedPath) {
                    if (view.delegateModel.getRoot() instanceof GUIBranchNode) {
                        TreeNode node = ((GUIAbstractTreeNode) view.delegateModel.getRoot())
                                .findBranch(invokedNode);
                        if (node instanceof GUIBranchNode) {
                            view.selectBranchNode((GUIBranchNode) node);
                        }
                    }
                } else {
                    view.delegateView.scrollPathToVisible(selectedPath);
                    view.delegateView.setSelectionPath(selectedPath);
                }
            } else {
                view.delegateModel.setFilter(filter, selected);
                if (branch == selectedPath) {
                    if (/* e.getStateChange() != ItemEvent.SELECTED */ !selected) {
                        if (view.delegateModel.getRoot() instanceof GUIBranchNode) {
                            TreeNode node = ((GUIAbstractTreeNode) view.delegateModel.getRoot())
                                    .findBranch(invokedNode);
                            if (node instanceof GUIBranchNode) {
                                view.selectBranchNode((GUIBranchNode) node);
                            }
                        }
                    } else {
                        if (invokedNode.parent() == null || view.delegateModel
                                .getProofTreeNode(invokedNode.parent())
                                .findChild(invokedNode.parent()) == null) {
                            // it's still a branch
                            if (view.delegateModel.getRoot() instanceof GUIBranchNode) {
                                TreeNode node =
                                        ((GUIAbstractTreeNode) view.delegateModel.getRoot())
                                                .findBranch(invokedNode);
                                if (node instanceof GUIBranchNode) {
                                    view.selectBranchNode((GUIBranchNode) node);
                                }
                            }
                        } else {
                            TreePath tp = new TreePath(view.delegateModel
                                    .getProofTreeNode(invokedNode).getPath());
                            view.delegateView.scrollPathToVisible(tp);
                            view.delegateView.setSelectionPath(tp);
                        }
                    }
                } else {
                    TreePath tp = new TreePath(
                            view.delegateModel.getProofTreeNode(invokedNode).getPath());
                    view.delegateView.scrollPathToVisible(tp);
                    view.delegateView.setSelectionPath(tp);
                }
            }
        }
    }

    static class Search extends ProofTreeSettings {
        private static final long serialVersionUID = -6543488911281521583L;

        public Search(ProofTreeView view) {
            super(view);
            setName("Search");
            setIcon(IconFactory.search2(ICON_SIZE));
            setAcceleratorKey(de.uka.ilkd.key.gui.prooftree.ProofTreeView.searchKeyStroke);
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            view.showSearchPanel();
        }
    }

    static class CollapseAll extends ProofTreeSettings {
        private static final long serialVersionUID = 5343671322035834491L;

        public CollapseAll(ProofTreeView view) {
            super(view);
            setName("Collapse All");
            setIcon(IconFactory.minus(ICON_SIZE));
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            ProofTreeExpansionState.collapseAll(view.delegateView);
            view.delegateView.expandRow(0);
        }
    }

    static class ExpandGoals extends ProofTreeSettings {
        private static final long serialVersionUID = -8404655108317574685L;

        public ExpandGoals(ProofTreeView view) {
            super(view);
            setName("Expand Goals Only");
            setIcon(IconFactory.expandGoals(ICON_SIZE));
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            Proof proof = view.getMediator().getSelectedProof();
            if (proof != null) {
                for (final Goal g : proof.openGoals()) {
                    view.makeNodeExpanded(g.node());
                }
                view.collapseClosedNodes();
                // do not show selected node if it is not on the path to an
                // open goal, but do expand root
                // makeNodeVisible(mediator.getSelectedNode());
                view.delegateView.expandRow(0);
            }
        }
    }

    static class TacletInfoToggle extends ProofTreeSettings {
        private static final long serialVersionUID = 1L;

        public TacletInfoToggle(ProofTreeView view) {
            super(view);
            setName("Show taclet info (inner nodes only)");
            setSelected(MainWindow.getInstance().isShowTacletInfo());
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            final boolean selected = isSelected();
            MainWindow.getInstance().setShowTacletInfo(selected);
        }
    }

    static abstract class ProofTreeSettings extends KeyAction {
        protected final ProofTreeView view;

        protected ProofTreeSettings(ProofTreeView view) {
            this.view = view;
        }
    }

    static class TreeSettingsAction extends KeyAction {
        TreeSettingsAction() {
            setName("Settings");
            putValue(SMALL_ICON, IconFactory.properties(MainWindow.TOOLBAR_ICON_SIZE));
        }

        @Override
        public void actionPerformed(ActionEvent e) {}
    }
}
