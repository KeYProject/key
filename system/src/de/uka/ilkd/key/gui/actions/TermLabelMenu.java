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

import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.pp.VisibleTermLabels;
import java.awt.Font;
import java.util.ArrayList;
import java.util.List;
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
    private final DisplayLabelsCheckBox displayLabelsCheckBox;

    public TermLabelMenu(final MainWindow mainWindow) {

        setText("Hide Term Labels");
        setToolTipText("Configure term label visibility.");
        checkBoxMap = new TreeMap<Name, TermLabelCheckBox>();
        this.mainWindow = mainWindow;

        displayLabelsCheckBox = new DisplayLabelsCheckBox(mainWindow);

        visibleTermLabels = new VisibleTermLabels() {
            @Override
            public boolean contains(Name name) {
                if (displayLabelsCheckBox.isSelected()) {
                   TermLabelCheckBox checkedName = checkBoxMap.get(name);
                   return checkedName != null && checkedName.isSelected();
                }
                else {
                   return false;
                }
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
        add(displayLabelsCheckBox);
        addSeparator();

        /*
         * Get sorted list of term label names.
         */
        List<Name> labelNames = mainWindow.getSortedTermLabelNames();

        /* 
         * Create list of {@link TermLabelCheckBox} instances.
         */
        ArrayList<TermLabelCheckBox> checkBoxList = new ArrayList<TermLabelCheckBox>();
        for (Name labelName : labelNames) {
            TermLabelCheckBox checkBox = checkBoxMap.get(labelName);
            if (checkBox == null) {
                checkBox = new TermLabelCheckBox(labelName);
                checkBoxMap.put(labelName, checkBox);
            }
            checkBoxList.add(checkBox);
        }

        /*
         * Add the checkboxes to the menu.
         */
        for (TermLabelCheckBox c : checkBoxList) {
            add(c);
        }
    }

    public VisibleTermLabels getVisibleTermLabels() {
        return visibleTermLabels;
    }

    private class DisplayLabelsCheckBox extends KeYMenuCheckBox {

        /**
         *
         */
        private static final long serialVersionUID = 8766949321781919880L;

        public DisplayLabelsCheckBox(MainWindow mainWindow) {
            super(mainWindow, "Display term labels in formulas", true);
            setTooltip("Use this checkbox to toggle visibility for all term labels.");
            setName("DisplayLabelsCheckBox");
        }

        @Override
        public void handleClickEvent() {
            for (JCheckBoxMenuItem checkBox : checkBoxMap.values()) {
                checkBox.setEnabled(isSelected());
            }
            mainWindow.makePrettyView();
        }

        @Override
        public final void setSelected(boolean b) {
            super.setSelected(b);
            handleClickEvent();
        }
    }

    private class TermLabelCheckBox extends KeYMenuCheckBox {

        /**
         *
         */
        private static final long serialVersionUID = 4582177241207958225L;

        // The name of the label, which belongs to this checkbox.
        private final Name labelName;

        // This String is used as ToolTipText in case the CheckBox is enabled.
        private String enabledToolTipText;

        TermLabelCheckBox(Name labelName) {
            super(mainWindow, labelName.toString(), true);
            this.labelName = labelName;
            setName(labelName.toString());
            setSelected(true);
            setEnabled(displayLabelsCheckBox.isSelected());
            mainWindow.loadPreferences(this);
            setItalicFont();
        }

        @Override
        public void handleClickEvent() {
            mainWindow.makePrettyView();
        }

        @Override
        public final void setEnabled(boolean b) {
            super.setEnabled(b);
            updateToolTipText();

        }

        private void setItalicFont() {
            setFont(getFont().deriveFont(Font.ITALIC));
            setEnabledToolTipText("Term label " + labelName + " does not occur in the current sequent.");
        }

        private void setBoldFont() {
            setFont(getFont().deriveFont(Font.BOLD));
            setEnabledToolTipText("Click to toggle visibility for term label " + labelName + ".");
        }

        /*
         * Define the text which is used in case this CheckBox is enabled.
         */
        private void setEnabledToolTipText(String s) {
            enabledToolTipText = s;
            updateToolTipText();
        }

        /*
         * Call this method in case ToolTipText needs to be updated.
         */
        private void updateToolTipText() {
            if (isEnabled()) {
                setToolTipText(enabledToolTipText);
            } else {
                setToolTipText("You turned off visibility for all term labels. "
                        + "This checkbox is disabled.");
            }
        }

    }
}
