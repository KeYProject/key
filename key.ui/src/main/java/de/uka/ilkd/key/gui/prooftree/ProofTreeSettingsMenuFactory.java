/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.prooftree;

import java.util.function.Supplier;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.docking.DynamicCMenu;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;

import bibliothek.gui.dock.common.action.CAction;
import bibliothek.gui.dock.common.action.CButton;
import bibliothek.gui.dock.common.action.CCheckBox;
import bibliothek.gui.dock.common.action.CMenu;

import static de.uka.ilkd.key.gui.prooftree.ProofTreePopupFactory.ICON_SIZE;

public class ProofTreeSettingsMenuFactory {
    private ProofTreeSettingsMenuFactory() {}

    public static CAction create(ProofTreeView view) {
        Supplier<CMenu> supplier = () -> {
            CMenu menu = new CMenu();

            menu.add(createSearch(view));
            menu.addSeparator();

            menu.add(createExpandAll(view));
            menu.add(createExpandGoals(view));
            menu.add(createCollapseAll(view));
            menu.addSeparator();

            for (ProofTreeViewFilter filter : ProofTreeViewFilter.ALL) {
                menu.add(createFilter(view, filter));
            }
            menu.addSeparator();

            menu.add(createExpandOSSToggle(view));
            menu.add(createTacletInfoToggle());
            return menu;
        };

        return new DynamicCMenu("Settings",
            IconFactory.properties(MainWindow.TOOLBAR_ICON_SIZE), supplier);
    }

    private static CButton createExpandAll(ProofTreeView view) {
        CButton button = new CButton();
        button.setText("Expand All");
        button.setIcon(IconFactory.plus(ICON_SIZE));
        button.addActionListener(e -> ProofTreeExpansionState.expandAll(view.delegateView,
            ProofTreePopupFactory.ossPathFilter(view.isExpandOSSNodes())));
        return button;
    }

    private static CCheckBox createFilter(ProofTreeView view, ProofTreeViewFilter filter) {
        CCheckBox check = new ProofTreeSettingsCheckBox();
        check.setText(filter.name());
        check.setEnabled(view.delegateModel != null);
        check.setSelected(filter.isActive());
        // add the selection listener *after* setting the initial value
        // (to avoid re-applying the filter)
        check.intern().addSelectableListener(
            (component, selected) -> check.setEnabled(view.setFilter(filter, check.isSelected())));
        return check;
    }

    private static CButton createSearch(ProofTreeView view) {
        CButton button = new CButton();
        button.setText("Search");
        button.setIcon(IconFactory.search2(ICON_SIZE));
        button.setAccelerator(de.uka.ilkd.key.gui.prooftree.ProofTreeView.SEARCH_KEY_STROKE);
        button.addActionListener(e -> view.showSearchPanel());
        return button;
    }

    private static CButton createCollapseAll(ProofTreeView view) {
        CButton button = new CButton();
        button.setText("Collapse All");
        button.setIcon(IconFactory.minus(ICON_SIZE));
        button.addActionListener(e -> {
            ProofTreeExpansionState.collapseAll(view.delegateView);
            view.delegateView.expandRow(0);
        });
        return button;
    }

    private static CButton createExpandGoals(ProofTreeView view) {
        CButton button = new CButton();
        button.setText("Expand Goals Only");
        button.setIcon(IconFactory.expandGoals(ICON_SIZE));
        button.addActionListener(e -> {
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
        });
        return button;
    }

    private static CCheckBox createExpandOSSToggle(ProofTreeView view) {
        CCheckBox check = new CCheckBox() {
            @Override
            protected void changed() {
                final boolean selected = isSelected();
                view.setExpandOSSNodes(selected);
            }
        };
        check.setText("Expand One Step Simplifications nodes");
        check.setSelected(view.isExpandOSSNodes());
        return check;
    }

    private static CCheckBox createTacletInfoToggle() {
        CCheckBox check = new CCheckBox() {
            @Override
            protected void changed() {
                final boolean selected = isSelected();
                MainWindow.getInstance().setShowTacletInfo(selected);
            }
        };
        check.setText("Show taclet info (inner nodes only)");
        check.setSelected(MainWindow.getInstance().isShowTacletInfo());
        return check;
    }

    /**
     * The checkbox used in the proof tree settings.
     *
     * @author Arne Keller
     */
    private static class ProofTreeSettingsCheckBox extends CCheckBox {
        @Override
        protected void changed() {
            // intentionally empty, a listener is added in the menu factory
        }
    }

}
