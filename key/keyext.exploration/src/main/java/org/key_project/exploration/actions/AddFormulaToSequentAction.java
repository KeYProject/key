package org.key_project.exploration.actions;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import org.key_project.exploration.ExplorationNodeData;
import org.key_project.util.collection.ImmutableList;

import java.awt.event.ActionEvent;

/**
 * Action to handle proof actions addition of formulas
 */
public class AddFormulaToSequentAction extends ExplorationAction {
    public AddFormulaToSequentAction(MainWindow mainWindow) {
        super(mainWindow);
    }



    @Override
    public void actionPerformed(ActionEvent e) {

    }

    /**
     * Add a formula to the antecedent -> unsound rule
     * @param t
     * @param antecedent whether to add to antecedent
     */
    /* void unsoundAddition(Term t, Boolean antecedent) {
        NoFindTacletBuilder builder = new NoFindTacletBuilder();
        Sequent addedFormula;
        if(antecedent) {
            builder.setName(new Name("add_formula_antec"));
            Semisequent semisequent = new Semisequent(new SequentFormula(t));
            addedFormula = Sequent.createAnteSequent(semisequent);
        } else {
            builder.setName(new Name("add_formula_succ"));
            Semisequent semisequent = new Semisequent(new SequentFormula(t));
            addedFormula = Sequent.createSuccSequent(semisequent);
        }


        ImmutableList<TacletGoalTemplate> templates = ImmutableSLList.nil();
        templates = templates.append(new TacletGoalTemplate(addedFormula, ImmutableSLList.nil()));
        builder.setTacletGoalTemplates(templates);
        Taclet taclet = builder.getTaclet();
        Goal g = getMediator().getSelectedGoal();
        ImmutableList<Goal> result = g.apply(NoPosTacletApp.createNoPosTacletApp(taclet));
        result.forEach(goal -> goal.node().getNodeInfo().setExploration(true));
    }*/

    /**
     * Create a new Tacletapp that is sound i.e. make a cut
     * @param t
     * @param antecedent whether to add to antecedent
     */
     void soundAddition(Term t, boolean antecedent, boolean showSecondBranch){
        Goal g = getMediator().getSelectedGoal();
        Taclet cut = getMediator().getSelectedProof().getEnv().getInitConfigForEnvironment().lookupActiveTaclet(new Name("cut"));
        Semisequent semisequent = new Semisequent(new SequentFormula(t));
        TacletApp app = NoPosTacletApp.createNoPosTacletApp(cut);
        SchemaVariable sv = app.uninstantiatedVars().iterator().next();
        app = app.addCheckedInstantiation(sv, semisequent.getFirst().formula(), getMediator().getServices(), true);
         g.node().getNodeInfo().register(new ExplorationNodeData(), ExplorationNodeData.class);

//         g.node().getNodeInfo().setExploration(true);
        ImmutableList<Goal> result = g.apply(app);
        //set the actions flag
         g.node().getNodeInfo().get(ExplorationNodeData.class).setExplorationAction("Add "+t);

         result.forEach(goal -> {
          //  goal.node().getNodeInfo().setExploration(true);
             goal.node().getNodeInfo().register(new ExplorationNodeData(), ExplorationNodeData.class);
             String s = goal.node().getNodeInfo().getBranchLabel();
            goal.node().getNodeInfo().setBranchLabel("ExplorationNode: " + s);

        });

        assert result.size() == 2;
        if(antecedent){
            Goal first = result.head();
            if(first.node().getNodeInfo().getBranchLabel().endsWith("FALSE")){
                first.setEnabled(false);
            } else {
                Goal second = result.tail().head();
                second.setEnabled(false);
            }
        } else {
            Goal first = result.head();
            if(first.node().getNodeInfo().getBranchLabel().endsWith("TRUE")){
                first.setEnabled(false);
            } else {
                Goal second = result.tail().head();
                second.setEnabled(false);
            }

        }

    }
}
