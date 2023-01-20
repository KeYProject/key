package org.key_project.exploration.actions;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Node;
import org.key_project.exploration.ProofExplorationService;

import javax.annotation.Nonnull;
import java.awt.event.ActionEvent;


/**
 * @author Alexander Weigl
 * @author Sarah Grebing
 * @version 1 (24.05.18)
 */
public class AddFormulaToSuccedentAction extends ExplorationAction {
    public AddFormulaToSuccedentAction() {
        this(MainWindow.getInstance());
    }

    public AddFormulaToSuccedentAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Add formula to succedent");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        Term t = promptForTerm(mainWindow, null);
        if (t == null)
            return;
        ProofExplorationService service = ProofExplorationService.get(getMediator());
        @Nonnull
        Node toBeSelected = service.soundAddition(getMediator().getSelectedGoal(), t, false);
        getMediator().getSelectionModel().setSelectedNode(toBeSelected);
    }
}
