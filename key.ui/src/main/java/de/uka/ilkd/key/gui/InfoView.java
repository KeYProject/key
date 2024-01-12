/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.awt.event.ComponentEvent;
import java.awt.event.ComponentListener;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import javax.swing.*;
import javax.swing.event.TreeSelectionEvent;
import javax.swing.event.TreeSelectionListener;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.core.KeYSelectionModel;
import de.uka.ilkd.key.gui.extension.api.DefaultContextMenuKind;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.gui.extension.impl.KeYGuiExtensionFacade;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.event.ProofDisposedEvent;
import de.uka.ilkd.key.proof.event.ProofDisposedListener;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.util.ThreadUtilities;
import de.uka.ilkd.key.util.XMLResources;

/**
 * Class for info contents displayed in {@link MainWindow}.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class InfoView extends JSplitPane implements TabPanel {

    private static final long serialVersionUID = -6944612837850368411L;
    public static final Icon INFO_ICON =
        IconFactory.INFO_VIEW.get(MainWindow.TAB_ICON_SIZE);


    private final InfoTree infoTree;
    private final InfoViewContentPane contentPane;
    private final XMLResources xmlResources;
    private final ProofDisposedListener proofDisposedListener;
    private final KeYSelectionListener selectionListener = new InfoViewSelectionListener();
    private Node lastShownGoalNode;
    private MainWindow mainWindow;
    private KeYMediator mediator;

    public InfoView() {
        super(VERTICAL_SPLIT);
        xmlResources = new XMLResources();

        // initial placement of the divider
        setDividerLocation(300);

        // growing goes to the upper half only
        setResizeWeight(1.0);

        // Setting a name for this causes PreferenceSaver to include this class.
        setName("infoViewPane");

        infoTree = new InfoTree();
        infoTree.addTreeSelectionListener(new TreeSelectionListener() {
            @Override
            public void valueChanged(TreeSelectionEvent e) {
                InfoTreeNode node = infoTree.getLastSelectedPathComponent();
                if (node != null) {
                    contentPane.setNode(node);
                } else {
                    contentPane.clear();
                }
            }
        });

        lastShownGoalNode = null;

        addComponentListener(new ComponentListener() {
            @Override
            public void componentShown(ComponentEvent e) {
                if (mediator.getSelectedProof() != null) {
                    Goal goal = mediator.getSelectedGoal();
                    if (goal != null) {
                        updateModel(mediator.getSelectedGoal());
                    }
                }
            }

            @Override
            public void componentResized(ComponentEvent e) {
            }

            @Override
            public void componentMoved(ComponentEvent e) {
            }

            @Override
            public void componentHidden(ComponentEvent e) {
            }
        });

        proofDisposedListener = new ProofDisposedListener() {
            @Override
            public void proofDisposing(ProofDisposedEvent e) {
            }

            @Override
            public void proofDisposed(ProofDisposedEvent e) {
                updateModel(null);
            }
        };

        infoTree.addMouseListener(new MouseAdapter() {
            public void mouseClicked(MouseEvent e) {
                checkPopup(e);
            }

            @Override
            public void mousePressed(MouseEvent e) {
                checkPopup(e);
            }

            private void checkPopup(MouseEvent e) {
                if (e.isPopupTrigger()) {
                    Rule selected = infoTree.getLastSelectedPathComponent().getRule();
                    JPopupMenu menu = KeYGuiExtensionFacade.createContextMenu(
                        DefaultContextMenuKind.TACLET_INFO, selected, mediator);
                    if (menu.getComponentCount() > 0) {
                        menu.show(InfoView.this, e.getX(), e.getY());
                    }
                }
            }
        });


        contentPane = new InfoViewContentPane();

        setLeftComponent(new JScrollPane(infoTree));
        setRightComponent(contentPane);

        KeYGuiExtensionFacade.installKeyboardShortcuts(mediator, this,
            KeYGuiExtension.KeyboardShortcuts.INFO_VIEW);
    }

    public InfoView(MainWindow window, KeYMediator mediator) {
        this();
        setMainWindow(window);
        setMediator(mediator);
    }



    public void setMediator(KeYMediator m) {
        assert m != null;
        if (mediator != null) {
            mediator.removeKeYSelectionListener(selectionListener);
        }
        m.addKeYSelectionListener(selectionListener);
        mediator = m;
    }

    public void setMainWindow(MainWindow w) {
        mainWindow = w;
    }

    @Override
    public String getTitle() {
        return "Info";
    }

    @Override
    public Icon getIcon() {
        return INFO_ICON;
    }

    @Override
    public JComponent getComponent() {
        return this;
    }

    private void updateModel(Goal g) {
        if (g == null || lastShownGoalNode != g.node()) {
            if (lastShownGoalNode != null) {
                lastShownGoalNode.proof().removeProofDisposedListener(proofDisposedListener);
            }
            final InfoTreeModel model;
            if (g != null) {
                model = new InfoTreeModel(g, xmlResources, mainWindow);
                g.proof().addProofDisposedListener(proofDisposedListener);
                lastShownGoalNode = g.node();
            } else {
                model = null;
                lastShownGoalNode = null;
            }
            contentPane.clear();
            infoTree.setModel(model);
        }
    }

    private class InfoViewSelectionListener implements KeYSelectionListener {

        /**
         * focused node has changed
         */
        @Override
        public void selectedNodeChanged(KeYSelectionEvent e) {
        }

        /**
         * the selected proof has changed (e.g. a new proof has been loaded)
         */
        @Override
        public void selectedProofChanged(KeYSelectionEvent e) {
            final KeYSelectionModel selectionModel = e.getSource();
            Runnable action = () -> {
                if (isVisible()) {
                    if (selectionModel.getSelectedProof() == null) {
                        updateModel(null);
                    } else if (selectionModel.getSelectedGoal() != null) {
                        // keep old view if an inner node has been selected
                        updateModel(selectionModel.getSelectedGoal());
                    }
                }
            };
            ThreadUtilities.invokeOnEventQueue(action);
        }

    }
}
