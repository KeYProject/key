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

    private final Map<Name, TermLabelCheckBox> checkBoxMap;
    private final MainWindow mainWindow;
    private final VisibleTermLabels visibleTermLabels;
    private final DisplayLabelsCheckBox displayLabelsCheckBox;

    public TermLabelMenu(final MainWindow mainWindow) {

        setText("Term Labels");
        setToolTipText("Configure term label visibility.");
        checkBoxMap = new TreeMap<Name, TermLabelCheckBox>();
        this.mainWindow = mainWindow;

        displayLabelsCheckBox = new DisplayLabelsCheckBox(mainWindow);

        visibleTermLabels = new VisibleTermLabels() {
            @Override
            public boolean contains(Name name) {
                return displayLabelsCheckBox.isSelected() && checkBoxMap.get(name).isSelected();
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

    private class DisplayLabelsCheckBox extends KeYMenuCheckBox {

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

    private class TermLabelCheckBox extends KeYMenuCheckBox implements Comparable<TermLabelCheckBox> {

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
        public int compareTo(TermLabelCheckBox t) {
            return mainWindowAction.getName().toLowerCase().
                    compareTo(t.mainWindowAction.getName().toLowerCase());
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
