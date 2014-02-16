// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 
package de.uka.ilkd.key.gui;

import javax.swing.JScrollPane;
import javax.swing.JSplitPane;
import javax.swing.event.TreeSelectionListener;

import de.uka.ilkd.key.util.GuiUtilities;
import javax.swing.event.TreeSelectionEvent;

public class InfoView extends JSplitPane {

    private InfoTreeModel infoTreeModel;
    private final InfoTree infoTree;
    private final InfoViewContentPane contentPane;
    private final KeYMediator mediator;

    public InfoView(KeYMediator mediator) {
        super(VERTICAL_SPLIT);

        this.mediator = mediator;
        mediator.addKeYSelectionListener(new SelectionListener());

        // initial placement of the divider
        setDividerLocation(300);

        // growing goes to the upper half only
        setResizeWeight(1.0);

        // Setting a name for this causes {@link PreferenceSaver} to store its preferences.
        setName("ruleViewPane");

        infoTree = new InfoTree();
        infoTree.addTreeSelectionListener(new TreeSelectionListener() {
            @Override
            public void valueChanged(TreeSelectionEvent e) {
                InfoTreeNode node = infoTree.getLastSelectedPathComponent();
                if (node != null) {
                    contentPane.setNode(node);
                }
            }
        });

        contentPane = new InfoViewContentPane();

        setLeftComponent(new JScrollPane(infoTree));
        setRightComponent(contentPane);

        setVisible(true);
    }

    private class SelectionListener implements KeYSelectionListener {

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
            Runnable action = new Runnable() {
                @Override
                public void run() {
                    if (mediator != null) {
                        if (mediator.getSelectedProof() != null) {
                            infoTreeModel = new InfoTreeModel(mediator.getSelectedGoal());
                            infoTree.setModel(infoTreeModel);
                        }
                    }
                }
            };
            GuiUtilities.invokeOnEventQueue(action);
        }

    }

}
