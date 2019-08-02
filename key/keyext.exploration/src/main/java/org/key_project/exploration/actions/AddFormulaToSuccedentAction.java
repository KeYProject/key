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
public class AddFormulaToSuccedentAction extends AddFormulaToSequentAction {

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
        Term t = promptForTerm(mainWindow, null);
        if (t == null) return;
        ExplorationModeModel model = getMediator().lookup(ExplorationModeModel.class);
        super.soundAddition(t, false);

/*        if (model.getExplorationTacletAppState()
                == ExplorationModeModel.ExplorationState.SIMPLIFIED_APP) {
            super.soundAddition(t, false, false);
        } else {
            super.soundAddition(t, false, true);
        }*/
    }


    /**
     * Create a new Tacletapp that is sound i.e. make a cut
     * @param t
     */
/*    private void soundAddition(Term t){
        Goal g = getMediator().getSelectedGoal();
        Taclet cut = getMediator().getSelectedProof().getEnv().getInitConfigForEnvironment().lookupActiveTaclet(new Name("cut"));
        Semisequent semisequent = new Semisequent(new SequentFormula(t));
        Sequent addedFormula = Sequent.createSuccSequent(semisequent);
        TacletApp app = NoPosTacletApp.createNoPosTacletApp(cut);
        SchemaVariable sv = app.uninstantiatedVars().iterator().next();
        app = app.addCheckedInstantiation(sv, semisequent.get(0).formula(), getMediator().getServices(), true);
        ImmutableList<Goal> result = g.apply(app);
        result.forEach(goal -> goal.node().getNodeInfo().setExploration(true));

    }*/
    //TODO change the focus and hide the cutformula = true branch

    /**
     * Create a new Tacletapplication that is possibly unsound
     * @param t
     */
/*    private void unsoundAddition(Term t) {
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
*/

}