package de.uka.ilkd.key.gui.actions;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.KeYSelectionEvent;
import de.uka.ilkd.key.gui.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.pp.TermLabelPreferences;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import javax.swing.JCheckBoxMenuItem;
import javax.swing.JMenu;

/**
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class TermLabelMenu extends JMenu {

    public final JCheckBoxMenuItem hideAllTermLabels;
    public final List<JCheckBoxMenuItem> checkBoxList;
    private final KeYMediator mediator;
    private final MainWindow mainWindow;
    public final TermLabelPreferences termLabelPreferences;

    private void rebuildMenu() {
        removeAll();
        checkBoxList.clear();
        add(hideAllTermLabels);

        if (mediator.getSelectedProof() != null) {
            addSeparator();
            Set<Class> termLabels = ITermLabel.getRegisteredTermLabels();
            List<String> stringNames = new LinkedList();
            for (Class c : termLabels) {
                KeYMenuCheckBox checkBox = new TermLabelCheckBox(c) {
                };
                checkBox.setSelected(!termLabelPreferences.hiddenTermLabels.contains(c));
                checkBox.setEnabled(!hideAllTermLabels.isSelected());
                add(checkBox);
                checkBoxList.add(checkBox);
            }
        }
    }

    public TermLabelMenu(final KeYMediator mediator, final MainWindow mainWindow) {

        this.setText("Term Labels");
        checkBoxList = new LinkedList();
        this.mainWindow = mainWindow;
        this.mediator = mediator;

        this.termLabelPreferences = new TermLabelPreferences() {
            @Override
            public boolean hideAllTermLabels() {
                return hideAllTermLabels.isSelected();
            }
        };

        hideAllTermLabels = new TermLabelToggleAction(mainWindow);
        hideAllTermLabels.setName("toggleTerms");

        mediator.addKeYSelectionListener(new KeYSelectionListener() {
            @Override
            public void selectedNodeChanged(KeYSelectionEvent e) {
            }

            @Override
            public void selectedProofChanged(KeYSelectionEvent e) {
                rebuildMenu();
            }
        });

        rebuildMenu();
    }

    private class TermLabelToggleAction extends KeYMenuCheckBox {

        public TermLabelToggleAction(MainWindow mainWindow) {
            super(mainWindow, "Hide all term labels");
            setTooltip("Turn off term labels, if not needed.");
        }

        @Override
        public void handleClickEvent() {
            for (JCheckBoxMenuItem checkBox : checkBoxList) {
                checkBox.setEnabled(!isSelected());
            }
            mainWindow.makePrettyView();
        }
    }

    private class TermLabelCheckBox extends KeYMenuCheckBox {

        Class c;

        TermLabelCheckBox(Class c) {
            super(mainWindow, c.getSimpleName());
            this.c = c;
        }

        @Override
        public void handleClickEvent() {
            if (isSelected()) {
                termLabelPreferences.hiddenTermLabels.remove(c);
            } else {
                termLabelPreferences.hiddenTermLabels.add(c);
            }
            mainWindow.makePrettyView();
        }

    }
}
