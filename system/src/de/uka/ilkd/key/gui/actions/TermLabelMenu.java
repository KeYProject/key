// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.actions;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.KeYSelectionEvent;
import de.uka.ilkd.key.gui.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.pp.VisibleTermLabels;
import java.awt.Font;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TreeMap;
import javax.swing.JCheckBoxMenuItem;
import javax.swing.JMenu;

/**
 * This menu can be used to toggle TermLabel visibility for the SequentView.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class TermLabelMenu extends JMenu {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;
    private final Map<Name, TermLabelCheckBox> checkBoxMap;
    private final MainWindow mainWindow;
    private final VisibleTermLabels visibleTermLabels;
    private final HideAllCheckBox hideAllCheckBox;

    public TermLabelMenu(final MainWindow mainWindow) {

        setText("Hide Term Labels");
        setToolTipText("Configure term label visibility.");
        checkBoxMap = new TreeMap<Name, TermLabelCheckBox>();
        this.mainWindow = mainWindow;

        hideAllCheckBox = new HideAllCheckBox(mainWindow);

        visibleTermLabels = new VisibleTermLabels() {
            @Override
            public boolean contains(Name name) {
                return !hideAllCheckBox.isSelected() && checkBoxMap.get(name).isSelected();
            }
        };

        rebuildMenu();

        mainWindow.getMediator().addKeYSelectionListener(new KeYSelectionListener() {

            /*
             * Change font style for TermLabelCheckBox instances when the selected node changes.
             */
            @Override
            public void selectedNodeChanged(KeYSelectionEvent e) {
                Set<Name> labelNames
                        = mainWindow.getMediator().getSelectedNode().sequent().getOccuringTermLabels();
                for (Entry<Name, TermLabelCheckBox> entry : checkBoxMap.entrySet()) {
                    TermLabelCheckBox checkBox = entry.getValue();
                    /*
                     * Font style indicates whether a label occurs in the currently displayed sequent.
                     */
                    if (labelNames.contains(entry.getKey())) {
                        checkBox.setBoldFont();
                    } else {
                        checkBox.setItalicFont();
                    }
                }
            }

            /*
             * This function only has effect if the Profile gets changed.
             */
            @Override
            public void selectedProofChanged(KeYSelectionEvent e) {
                rebuildMenu();
            }
        });
    }

    private void rebuildMenu() {
        removeAll();
        add(hideAllCheckBox);
        addSeparator();

        /* 
         * Get list of labels from profile. This list is not always identical,
         * since the used Profile may change during execution.
         */
        ImmutableList<Name> labelNamesFromProfile = mainWindow.getMediator()
                .getProfile().getTermLabelManager().getSupportedTermLabelNames();

        /* 
         * Add labels from Profile to checkBoxMap and checkBoxList.
         */
        ArrayList<TermLabelCheckBox> checkBoxList = new ArrayList<TermLabelCheckBox>();
        for (Name labelName : labelNamesFromProfile) {
            TermLabelCheckBox checkBox = checkBoxMap.get(labelName);
            if (checkBox == null) {
                checkBox = new TermLabelCheckBox(labelName);
                checkBoxMap.put(labelName, checkBox);
            }
            checkBox.setEnabled(!hideAllCheckBox.isSelected());
            checkBoxList.add(checkBox);
        }

        /*
         * Sort checkBoxList and add remaining menu entries.
         */
        Collections.sort(checkBoxList);
        for (TermLabelCheckBox c : checkBoxList) {
            add(c);
        }
    }

    public VisibleTermLabels getVisibleTermLabels() {
        return visibleTermLabels;
    }

    private class HideAllCheckBox extends KeYMenuCheckBox {

        public HideAllCheckBox(MainWindow mainWindow) {
            super(mainWindow, "Hide all term labels");
            setTooltip("Use this checkbox to toggle visibility for all term labels.");
            setName("hideAllCheckBox");
        }

        @Override
        public void handleClickEvent() {
            for (JCheckBoxMenuItem checkBox : checkBoxMap.values()) {
                checkBox.setEnabled(!isSelected());
            }
            mainWindow.makePrettyView();
        }

        @Override
        public void setSelected(boolean b) {
            super.setSelected(b);
            handleClickEvent();
        }
    }

    private class TermLabelCheckBox extends KeYMenuCheckBox implements Comparable<TermLabelCheckBox> {

        Name labelName;

        TermLabelCheckBox(Name labelName) {
            super(mainWindow, labelName.toString());
            this.labelName = labelName;
            setName(labelName.toString());
            setSelected(true);
            mainWindow.loadPreferences(this);
            setItalicFont();
        }

        @Override
        public void handleClickEvent() {
            mainWindow.makePrettyView();
        }

        @Override
        public int compareTo(TermLabelCheckBox t) {
            return mainWindowAction.getName().toLowerCase().
                    compareTo(t.mainWindowAction.getName().toLowerCase());
        }

        @Override
        public void setEnabled(boolean b) {
            if (!b) {
                setToolTipText("You turned off visibility for all term labels, "
                        + "which disables this checkbox.");
            }
            super.setEnabled(b);
        }

        private void setItalicFont() {
            setFont(getFont().deriveFont(Font.ITALIC));
            boolean enabled = !hideAllCheckBox.isSelected();
            if (enabled) {
                setToolTipText("Term label " + labelName + " does not occur in the current sequent.");
            }
            setEnabled(enabled);
        }

        private void setBoldFont() {
            setFont(getFont().deriveFont(Font.BOLD));
            boolean enabled = !hideAllCheckBox.isSelected();
            if (enabled) {
                setToolTipText("Click to toggle visibility for term label " + labelName + ".");
            }
            setEnabled(enabled);
        }

    }
}