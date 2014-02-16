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

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.Properties;

import javax.swing.JScrollPane;
import javax.swing.JSplitPane;
import javax.swing.JTextArea;
import javax.swing.event.TreeSelectionListener;

import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.InfoTreeModel;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.util.GuiUtilities;
import javax.swing.BorderFactory;
import javax.swing.event.TreeSelectionEvent;

public class InfoView extends JSplitPane {

    private static final String DESC_RESOURCE = "/de/uka/ilkd/key/gui/help/ruleExplanations.xml";
    private InfoTreeModel infoTreeModel;
    private final InfoTree infoTree;
    private final JTextArea contentPane;
    private final JScrollPane contentScrollPane;
    private final KeYMediator mediator;
    private final XMLProperties ruleExplanations;

    public InfoView(KeYMediator mediator) {
        super(VERTICAL_SPLIT);

        this.mediator = mediator;
        mediator.addKeYSelectionListener(new SelectionListener());
        ruleExplanations = new XMLProperties(DESC_RESOURCE);

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

                    Object userObj = node.getUserObject();

                    String descriptionTitle;
                    String description;

                    if (userObj instanceof Rule) {
                        descriptionTitle = ((Rule) userObj).displayName();
                    } else {
                        descriptionTitle = userObj.toString();
                    }

                    if (userObj instanceof Taclet) {
                        Taclet tac = (Taclet) userObj;
                        description = getDescriptionFromTaclet(tac);
                    } else {
                        int parenIdx = descriptionTitle.lastIndexOf("(");
                        if (parenIdx >= 0) // strip number of taclets
                        {
                            descriptionTitle = descriptionTitle.substring(0, parenIdx - 1).intern();
                        }
                        description = getRuleDescription(descriptionTitle);
                    }

                    contentScrollPane.setBorder(BorderFactory.createTitledBorder(descriptionTitle));
                    contentPane.setText(description);
                    contentPane.setCaretPosition(0);
                }
            }
        });

        contentPane = new JTextArea("", 15, 30);
        contentPane.setEditable(false);
        contentPane.setLineWrap(true);
        contentPane.setWrapStyleWord(true);
        contentScrollPane = new JScrollPane(contentPane);

        setLeftComponent(new JScrollPane(infoTree));
        setRightComponent(contentScrollPane);

        setVisible(true);
    }

    private String getRuleDescription(String name) {
        String desc = ruleExplanations.getProperty(name);
        if (desc == null) {
            return "No description available for " + name;
        } else {
            return desc;
        }
    }

    private static String getDescriptionFromTaclet(Taclet tac) {
        LogicPrinter lp = new LogicPrinter(new ProgramPrinter(), new NotationInfo(), null, true);
        lp.printTaclet(tac);
        return lp.toString();
    }

    protected void setRuleTreeModel(InfoTreeModel model) {
        infoTreeModel = model;
        if (infoTreeModel != null) {
            infoTreeModel.updateTacletCount();
            infoTree.setModel(infoTreeModel);
        }
    }

    private class SelectionListener implements KeYSelectionListener {

        /**
         * focused node has changed
         */
        @Override
        public void selectedNodeChanged(KeYSelectionEvent e) {
            infoTreeModel.setSelectedGoal(e.getSource().getSelectedGoal());
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
                            setRuleTreeModel(new InfoTreeModel(mediator.getSelectedGoal()));
                        } else {
                            infoTreeModel.setSelectedGoal(null);
                        }
                    }
                }
            };
            GuiUtilities.invokeOnEventQueue(action);
        }

    }

    /*
     * Use this class to get descriptions from an XML file.
     */
    private static class XMLProperties extends Properties {

        XMLProperties(String xmlFile) {
            InputStream is = getClass().getResourceAsStream(xmlFile);
            try {
                if (is == null) {
                    throw new FileNotFoundException("Descriptions file " + xmlFile + " not found.");
                }
                loadFromXML(is);
            } catch (IOException e) {
                System.err.println("Cannot not load help messages in info view");
                e.printStackTrace();
            }
        }
    }

}
