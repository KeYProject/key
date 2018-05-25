package de.uka.ilkd.key.gui.actions.exploration;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.proofExploration.ExplorationModeModel;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.tacletbuilder.NoFindTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import javax.swing.*;
import java.awt.event.ActionEvent;
import java.io.Reader;
import java.io.StringReader;

/**
 * Action to handle proof exploration addition of formulas
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
     void unsoundAddition(Term t, Boolean antecedent) {
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
    }

    /**
     * Create a new Tacletapp that is sound i.e. make a cut
     * @param t
     * @param antecedent whether to add to antecedent
     */
     void soundAddition(Term t, boolean antecedent){
        Goal g = getMediator().getSelectedGoal();
        Taclet cut = getMediator().getSelectedProof().getEnv().getInitConfigForEnvironment().lookupActiveTaclet(new Name("cut"));
        Semisequent semisequent = new Semisequent(new SequentFormula(t));
        TacletApp app = NoPosTacletApp.createNoPosTacletApp(cut);
        SchemaVariable sv = app.uninstantiatedVars().iterator().next();
        app = app.addCheckedInstantiation(sv, semisequent.getFirst().formula(), getMediator().getServices(), true);
        ImmutableList<Goal> result = g.apply(app);
        result.forEach(goal -> goal.node().getNodeInfo().setExploration(true));
        assert result.size() == 2;
        if(antecedent){
            Goal first = result.head();
            if(first.node().getNodeInfo().getBranchLabel().endsWith("FALSE")){
                first.setEnabled(false);
                //TODO now hide the branch
            } else {
                Goal second = result.tail().head();
                second.setEnabled(false);
            }
        }

    }
}
