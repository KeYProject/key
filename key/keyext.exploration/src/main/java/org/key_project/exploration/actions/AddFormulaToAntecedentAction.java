package org.key_project.exploration.actions;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.logic.Term;
import org.key_project.exploration.ExplorationModeModel;

import java.awt.event.ActionEvent;

/**
 * @author Alexander Weigl
 * @author Sarah Grebing
 * @version 1 (24.05.18)
 */
public class AddFormulaToAntecedentAction extends AddFormulaToSequentAction {

    public AddFormulaToAntecedentAction() {
        this(MainWindow.getInstance());
    }

    public AddFormulaToAntecedentAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Add formula to antecedent");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        Term t = promptForTerm(mainWindow, null);
        if (t == null) return;
        ExplorationModeModel model = getMediator().get(ExplorationModeModel.class);
        super.soundAddition(t, true);

/*        if (model.getExplorationTacletAppState()
                == (ExplorationModeModel.ExplorationState.SIMPLIFIED_APP)) {
            super.soundAddition(t, true, false);
        } else {
            super.soundAddition(t, true, true);
        }*/
    }
}
