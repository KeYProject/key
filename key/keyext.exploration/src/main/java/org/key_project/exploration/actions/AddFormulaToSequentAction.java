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
 * ExplorationAction that handles the addition of formulas to the sequent.
 * This action is implemented using the cut rule.
 *
 * The branch not corresponding to the desried change is set to interactive. This enables that the automatic strategies
 * avoid expanding this branch and the user needs to activate the branch by hand.
 *
 * Adding formulas to the antecedent:
 *  '==> p' as goal node and adding q to the antecedent results in two branches:
 *
 * 1) q ==> p
 * 2) ==> p,q <-- this branch is set to interactive such that the automatic strategies do not expand it

 * Adding formulas to the succedent:
 *  '==> p' as goal node and adding q to the succedent results in two branches:
 *
 * 1) q ==> p <-- this branch is set to interactive such that the automatic strategies do not expand it
 * 2) ==> p,q
 *
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
     * Create a new Tacletapp that add a formula to the sequent using the cut rule and disabeling one of the branches
     * @param t Term to add to teh sequent
     * @param antecedent whether to add teh term to antecedent
     */
     void soundAddition(Term t, boolean antecedent){
        Goal g = getMediator().getSelectedGoal();
        Taclet cut = getMediator().getSelectedProof().getEnv().getInitConfigForEnvironment().lookupActiveTaclet(new Name("cut"));
        Semisequent semisequent = new Semisequent(new SequentFormula(t));
        TacletApp app = NoPosTacletApp.createNoPosTacletApp(cut);
        SchemaVariable sv = app.uninstantiatedVars().iterator().next();
        app = app.addCheckedInstantiation(sv, semisequent.getFirst().formula(), getMediator().getServices(), true);
        ExplorationNodeData explorationNodeData = new ExplorationNodeData();
        if(antecedent)
            explorationNodeData.setExplorationAction("Added "+t+ " ==>");
        else
            explorationNodeData.setExplorationAction("Added ==> "+t);

         g.node().getNodeInfo().register(explorationNodeData, ExplorationNodeData.class);

        ImmutableList<Goal> result = g.apply(app);

        //set the actions flag
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
                getMediator().getSelectionModel().setSelectedNode(result.tail().head().node());
            } else {
                Goal second = result.tail().head();
                second.setEnabled(false);
                getMediator().getSelectionModel().setSelectedNode(result.head().node());
            }
        } else {
            Goal first = result.head();
            if(first.node().getNodeInfo().getBranchLabel().endsWith("TRUE")){
                first.setEnabled(false);
                getMediator().getSelectionModel().setSelectedNode(result.tail().head().node());
            } else {
                Goal second = result.tail().head();
                second.setEnabled(false);
                getMediator().getSelectionModel().setSelectedNode(result.head().node());
            }

        }

    }
}
