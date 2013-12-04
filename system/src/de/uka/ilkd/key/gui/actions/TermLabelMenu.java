package de.uka.ilkd.key.gui.actions;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.pp.VisibleTermLabels;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Map;
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

    public TermLabelMenu(final MainWindow mainWindow) {

        setText("Term Labels");
        checkBoxMap = new TreeMap<Name, TermLabelCheckBox>();
        this.mainWindow = mainWindow;

        final HideAllCheckBox hideAllCheckBox = new HideAllCheckBox(mainWindow);
        add(hideAllCheckBox);

        visibleTermLabels = new VisibleTermLabels() {
            @Override
            public boolean contains(Name name) {
                return !hideAllCheckBox.isSelected() && checkBoxMap.get(name).isSelected();
            }
        };

        addSeparator();
        for (Name labelName
                : mainWindow.getMediator()
                .getProfile().getTermLabelManager().getSupportedTermLabelNames()) {
            TermLabelCheckBox checkBox = new TermLabelCheckBox(labelName);
            checkBox.setSelected(true);
            checkBox.setEnabled(!hideAllCheckBox.isSelected());
            checkBoxMap.put(labelName, checkBox);
        }
        ArrayList<TermLabelCheckBox> checkBoxList
                = new ArrayList<TermLabelCheckBox>(checkBoxMap.values());
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
            setTooltip("Turn off term labels, if not needed.");
            setName("hideAllCheckBox");
        }

        @Override
        public void handleClickEvent() {
            for (JCheckBoxMenuItem checkBox : checkBoxMap.values()) {
                checkBox.setEnabled(!isSelected());
            }
            mainWindow.makePrettyView();
        }
    }

    private class TermLabelCheckBox extends KeYMenuCheckBox implements Comparable<TermLabelCheckBox> {

        Name labelName;

        TermLabelCheckBox(Name labelName) {
            super(mainWindow, labelName.toString());
            this.labelName = labelName;
            setName(labelName.toString());
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
    }
}
