package de.uka.ilkd.key.gui.actions.exploration;

import de.uka.ilkd.key.gui.ExplorationModeToolBar;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.NoFindTaclet;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.tacletbuilder.NoFindTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import java.awt.event.ActionEvent;

import static de.uka.ilkd.key.gui.actions.exploration.AddFormulaToAntecedentAction.promptForTerm;
import org.key_project.util.collection.ImmutableSet;

/**
 * @author Alexander Weigl
 * @author Sarah Grebing
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
        if(mainWindow.explorationToolBar.getExplorationTacletAppState()
                == (ExplorationModeToolBar.ExplorationState.UNSOUND_APPS)) {
            unsoundAddition(t);
        } else {
            soundAddition(t);
        }
    }


    /**
     * Create a new Tacletapp that is sound i.e. make a cut
     * @param t
     */
    private void soundAddition(Term t){
        Goal g = getMediator().getSelectedGoal();
        Taclet cut = getMediator().getSelectedProof().getEnv().getInitConfigForEnvironment().lookupActiveTaclet(new Name("cut"));
        Semisequent semisequent = new Semisequent(new SequentFormula(t));
        Sequent addedFormula = Sequent.createSuccSequent(semisequent);
        TacletApp app = NoPosTacletApp.createNoPosTacletApp(cut);
        SchemaVariable sv = app.uninstantiatedVars().iterator().next();
        app = app.addCheckedInstantiation(sv, semisequent.get(0).formula(), getMediator().getServices(), true);
        ImmutableList<Goal> result = g.apply(app);
        result.forEach(goal -> goal.node().getNodeInfo().setExploration(true));

    }   //TODO change the focus and hide the cutformula = true branch

    /**
     * Create a new Tacletapplication that is possibly unsound
     * @param t
     */
    private void unsoundAddition(Term t) {
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