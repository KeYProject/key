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

    private static final String RULE_RESOURCE = "/de/uka/ilkd/key/gui/help/ruleExplanations.xml";
    private final XMLProperties ruleExplanations;

    private static final String LABEL_RESOURCE = "/de/uka/ilkd/key/gui/help/termLabelExplanations.xml";
    private final XMLProperties termLabelExplanations;

    private final InfoTree infoTree;
    private final InfoViewContentPane contentPane;
    private final KeYMediator mediator;
    private final MainWindow mainWindow;

    public InfoView(KeYMediator mediator, MainWindow mainWindow) {
        super(VERTICAL_SPLIT);
        assert mediator != null;
        ruleExplanations = new XMLProperties(RULE_RESOURCE);
        termLabelExplanations = new XMLProperties(LABEL_RESOURCE);
        this.mainWindow = mainWindow;
        this.mediator = mediator;
        mediator.addKeYSelectionListener(new SelectionListener());

        // initial placement of the divider
        setDividerLocation(300);

        // growing goes to the upper half only
        setResizeWeight(1.0);

        // Setting a name for this causes PreferenceSaver to include this class.
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
                    if (mediator.getSelectedProof() != null) {
                        infoTree.setModel(new InfoTreeModel(mediator.getSelectedGoal(),
                                ruleExplanations, termLabelExplanations, mainWindow));
                    }
                }
            };
            GuiUtilities.invokeOnEventQueue(action);
        }

    }

}
