package de.uka.ilkd.key.gui.actions.exploration;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.proofExploration.ExplorationModeModel;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import java.awt.event.ActionEvent;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Set;

/**
 * @author Alexander Weigl
 * @version 1 (24.05.18)
 */
public class EditFormulaAction extends ExplorationAction {
    private final PosInSequent posInSeq;

    public EditFormulaAction(PosInSequent pis) {
        this(pis, MainWindow.getInstance());
    }

    public EditFormulaAction(PosInSequent pis, MainWindow mainWindow) {
        super(mainWindow);
        setName("Edit formula");
        this.posInSeq = pis;
        setEnabled(!pis.isSequent());
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        if (posInSeq.isSequent()) return;

        PosInOccurrence pio = posInSeq.getPosInOccurrence();
        Term term = pio.subTerm();
        Goal g = getMediator().getSelectedGoal();

        Term newTerm = promptForTerm(mainWindow,
                LogicPrinter.quickPrintTerm(term, getMediator().getServices()));

        if (newTerm == null) {
            return;
        }

        TacletApp app;
        if(getMediator().getExplorationModeModel().getExplorationTacletAppState() == ExplorationModeModel.ExplorationState.SOUND_APPS){
            app = soundChange(pio, term, newTerm);
        } else {
            app = changeFormula(pio, newTerm);

        }
        ImmutableList<Goal> result = g.apply(app);
        result.forEach(goal -> goal.node().getNodeInfo().setExploration(true));
    }

    private TacletApp soundChange(PosInOccurrence pio, Term term, Term newTerm) {
        Taclet cut = getMediator().getSelectedProof().getEnv().getInitConfigForEnvironment().lookupActiveTaclet(new Name("cut"));
        TermBuilder tb = new TermBuilder(new TermFactory(new HashMap<>()), getMediator().getServices());
        Term concat = tb.equals(term, newTerm);
        Semisequent semisequent = new Semisequent(new SequentFormula(concat));
        TacletApp app = NoPosTacletApp.createNoPosTacletApp(cut);
        SchemaVariable sv = app.uninstantiatedVars().iterator().next();
        app = app.addCheckedInstantiation(sv, semisequent.getFirst().formula(), getMediator().getServices(), true);
        /*if(antecedent){
            Goal first = result.head();
            if(first.node().getNodeInfo().getBranchLabel().endsWith("FALSE")){
                first.setEnabled(false);
                //TODO now hide the branch
            } else {
                Goal second = result.tail().head();
                second.setEnabled(false);
            }
        }*/
        return app;
    }

    public TacletApp changeFormula(PosInOccurrence pos, Term replaceWith) {
        RewriteTacletBuilder changeBuilder = new RewriteTacletBuilder();
        changeBuilder.setName(new Name("change_formula"));
        changeBuilder.setFind(pos.subTerm());

        ImmutableList<RewriteTacletGoalTemplate> templates = ImmutableSLList.nil();
        templates = templates.append(new RewriteTacletGoalTemplate(replaceWith));
        changeBuilder.setTacletGoalTemplates(templates);

        FindTaclet taclet = changeBuilder.getTaclet();
        Set<SchemaVariable> svs = taclet.collectSchemaVars();
        Iterator<SchemaVariable> it = svs.iterator();
        TacletApp tacapp = PosTacletApp.createPosTacletApp(taclet,
                SVInstantiations.EMPTY_SVINSTANTIATIONS, pos, getMediator().getServices());
        if (it.hasNext()) {
            tacapp = tacapp.addCheckedInstantiation(it.next(),
                    pos.sequentFormula().formula(), getMediator().getServices(), false);
        }
        return tacapp;
    }
}
