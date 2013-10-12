package de.uka.ilkd.key.gui.actions;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.KeYSelectionEvent;
import de.uka.ilkd.key.gui.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.pp.LogicPrinter;
import java.awt.event.ActionEvent;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
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

    private void rebuildMenu() {
        removeAll();
        checkBoxList.clear();
        add(hideAllTermLabels);

        if (mediator.getSelectedProof() != null) {
            addSeparator();
            ImmutableList<Name> termLabelNames
                    = mediator.getSelectedProof().env().
                    getInitConfig().getProfile().getSupportedLabelNames();
            List<String> stringNames = new LinkedList();
            for (Name name : termLabelNames) {
                stringNames.add(name.toString());
            }
            Collections.sort(stringNames);
            for (final String name : stringNames) {

                KeYMenuCheckBox checkBox = new KeYMenuCheckBox(mainWindow, name) {
                    @Override
                    public void checkBoxToggled() {
                        if (isSelected()) {
                            LogicPrinter.hiddenTermLabels.remove(name);
                        } else {
                            LogicPrinter.hiddenTermLabels.add(name);
                        }
                        mainWindow.makePrettyView();
                    }
                };
                checkBox.setName(name);
                checkBox.setSelected(true);
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
        public void checkBoxToggled() {
            for (JCheckBoxMenuItem checkBox : checkBoxList) {
                checkBox.setEnabled(!isSelected());
            }
            mainWindow.makePrettyView();
        }

    }

}
