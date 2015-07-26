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

import java.awt.event.ComponentEvent;
import java.awt.event.ComponentListener;

import javax.swing.JScrollPane;
import javax.swing.JSplitPane;
import javax.swing.event.TreeSelectionEvent;
import javax.swing.event.TreeSelectionListener;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.core.KeYSelectionModel;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.event.ProofDisposedEvent;
import de.uka.ilkd.key.proof.event.ProofDisposedListener;
import de.uka.ilkd.key.util.ThreadUtilities;
import de.uka.ilkd.key.util.XMLResources;

/**
 * Class for info contents displayed in {@link MainWindow}.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class InfoView extends JSplitPane {

    /**
     *
     */
    private static final long serialVersionUID = -6944612837850368411L;
    
    private Node lastShownGoalNode; 
    private final InfoTree infoTree;
    private final InfoViewContentPane contentPane;
    private final MainWindow mainWindow;
    private final XMLResources xmlResources;
    private final ProofDisposedListener proofDisposedListener;

    public InfoView(final KeYMediator mediator, MainWindow mainWindow) {
        super(VERTICAL_SPLIT);
        assert mediator != null;
        xmlResources = new XMLResources();
        this.mainWindow = mainWindow;
        mediator.addKeYSelectionListener(new InfoViewSelectionListener());

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
            public void componentMoved(ComponentEvent e) { }
            
            @Override
            public void componentHidden(ComponentEvent e) { }
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

        
        contentPane = new InfoViewContentPane();

        setLeftComponent(new JScrollPane(infoTree));
        setRightComponent(contentPane);
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
            Runnable action = new Runnable() {
                @Override
                public void run() {
                    if (isVisible()) {
                        if (selectionModel.getSelectedProof() == null) {
                            updateModel(null);
                        } else if (selectionModel.getSelectedGoal() != null) {
                            // keep old view if an inner node has been selected
                            updateModel(selectionModel.getSelectedGoal());
                        }
                    }
                }
            };
            ThreadUtilities.invokeOnEventQueue(action);
        }

    }

    private void updateModel(Goal g) {                
        if (g == null || lastShownGoalNode != g.node()) {
            if (lastShownGoalNode != null) {
                lastShownGoalNode.proof().removeProofDisposedListener(proofDisposedListener);
            }
            final InfoTreeModel model;
            if ( g != null ) {
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
}
