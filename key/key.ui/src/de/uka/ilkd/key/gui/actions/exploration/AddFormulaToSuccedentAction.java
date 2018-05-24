package de.uka.ilkd.key.gui.actions.exploration;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.NoFindTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import java.awt.event.ActionEvent;

import static de.uka.ilkd.key.gui.actions.exploration.AddFormulaToAntecedentAction.promptForTerm;

/**
 * @author Alexander Weigl
 * @version 1 (24.05.18)
 */
public class AddFormulaToSuccedentAction extends MainWindowAction {

    /**
     *
     */
    public AddFormulaToSuccedentAction() {
        this(MainWindow.getInstance());
    }

    /**
     * @param mainWindow
     */
    public AddFormulaToSuccedentAction(MainWindow mainWindow) {
        super(mainWindow);

        setName("Add formula to succedent");
    }


    @Override
    public void actionPerformed(ActionEvent e) {
        Term t = promptForTerm(mainWindow, "");
        if (t == null) return;
        NoFindTacletBuilder builder = new NoFindTacletBuilder();
        builder.setName(new Name("add_formula_succ"));
        Semisequent semisequent = new Semisequent(new SequentFormula(t));
        Sequent addedFormula = Sequent.createSuccSequent(semisequent);
        ImmutableList<TacletGoalTemplate> templates = ImmutableSLList.nil();
        templates = templates.append(new TacletGoalTemplate(addedFormula, ImmutableSLList.nil()));
        builder.setTacletGoalTemplates(templates);
        Taclet taclet = builder.getTaclet();
        Goal g = getMediator().getSelectedGoal();
        ImmutableList<Goal> result = g.apply(NoPosTacletApp.createNoPosTacletApp(taclet));
        result.forEach(goal -> goal.node().getNodeInfo().setExploration(true));
    }
}