/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.*;
import java.util.*;
import java.util.List;
import java.util.Map.Entry;
import javax.swing.*;

import de.uka.ilkd.key.control.TermLabelVisibilityManager;
import de.uka.ilkd.key.control.event.TermLabelVisibilityManagerEvent;
import de.uka.ilkd.key.control.event.TermLabelVisibilityManagerListener;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.logic.Name;

/**
 * This menu can be used to toggle TermLabel visibility for the SequentView.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class TermLabelMenu extends JMenu {
    public static final String TERM_LABEL_MENU = "Term Labels";

    /**
     *
     */
    private static final long serialVersionUID = 1L;
    private final TermLabelVisibilityManager visibleTermLabels = new TermLabelVisibilityManager();
    private final Map<Name, TermLabelCheckBox> checkBoxMap = new TreeMap<>();
    private final MainWindow mainWindow;
    private final DisplayLabelsCheckBox displayLabelsCheckBox;

    /**
     * Observes changes on {@link #visibleTermLabels}.
     */
    private final TermLabelVisibilityManagerListener termLabelVisibilityManagerListener =
        this::handleVisibleLabelsChanged;

    public TermLabelMenu(final MainWindow mainWindow) {
        this.mainWindow = mainWindow;
        setText(TERM_LABEL_MENU);
        setToolTipText("Configure term label visibility.");
        visibleTermLabels.addTermLabelVisibilityManagerListener(termLabelVisibilityManagerListener);

        displayLabelsCheckBox = new DisplayLabelsCheckBox(mainWindow);

        rebuildMenu();

        mainWindow.getMediator().addKeYSelectionListener(new KeYSelectionListener() {

            /*
             * Change font style for TermLabelCheckBox instances when the selected node changes.
             */
            @Override
            public void selectedNodeChanged(KeYSelectionEvent e) {
                Set<Name> labelNames =
                    mainWindow.getMediator().getSelectedNode().sequent().getOccuringTermLabels();
                for (Entry<Name, TermLabelCheckBox> entry : checkBoxMap.entrySet()) {
                    TermLabelCheckBox checkBox = entry.getValue();
                    /*
                     * Font style indicates whether a label occurs in the currently displayed
                     * sequent.
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

    /**
     * When the visible term labels have changed.
     * <p>
     * <b>Attention:</b> This can happen in an Eclipse context outside of the checkbox items!
     *
     * @param e The event object.
     */
    protected void handleVisibleLabelsChanged(TermLabelVisibilityManagerEvent e) {
        if (displayLabelsCheckBox != null) {
            displayLabelsCheckBox.setSelected(visibleTermLabels.isShowLabels());
        }
        for (TermLabelCheckBox box : checkBoxMap.values()) {
            box.setEnabled(visibleTermLabels.isShowLabels());
            box.setSelected(!visibleTermLabels.isHidden(box.labelName));
        }
        mainWindow.makePrettyView();
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
        ArrayList<TermLabelCheckBox> checkBoxList = new ArrayList<>();
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

    public TermLabelVisibilityManager getVisibleTermLabels() {
        return visibleTermLabels;
    }

    public class DisplayLabelsCheckBox extends KeYMenuCheckBox {
        public static final String LABEL = "Display Term Labels in Formulas";

        public static final String TOOL_TIP =
            "Use this checkbox to toggle visibility for all term labels.";

        /**
         *
         */
        private static final long serialVersionUID = 8766949321781919880L;

        private DisplayLabelsCheckBox(MainWindow mainWindow) {
            super(mainWindow, LABEL, true);
            setTooltip(TOOL_TIP);
            setName("DisplayLabelsCheckBox");
            setSelected(visibleTermLabels.isShowLabels());
        }

        @Override
        public void handleClickEvent() {
            boolean selected = isSelected();
            visibleTermLabels.setShowLabels(selected);
            for (JCheckBoxMenuItem checkBox : checkBoxMap.values()) {
                checkBox.setEnabled(selected);
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
            setSelected(!visibleTermLabels.isHidden(labelName));
            setEnabled(displayLabelsCheckBox.isSelected());
            mainWindow.loadPreferences(this);
            visibleTermLabels.setHidden(labelName, !isSelected());
            setItalicFont();
        }

        @Override
        public void handleClickEvent() {
            visibleTermLabels.setHidden(labelName, !isSelected());
            mainWindow.makePrettyView();
        }

        @Override
        public final void setEnabled(boolean b) {
            super.setEnabled(b);
            updateToolTipText();
        }

        private void setItalicFont() {
            setFont(getFont().deriveFont(Font.ITALIC));
            setEnabledToolTipText(
                "Term label " + labelName + " does not occur in the current sequent.");
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
