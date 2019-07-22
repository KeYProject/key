package org.key_project.exploration.actions;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.*;
import org.key_project.exploration.ExplorationNodeData;
import org.key_project.util.collection.ImmutableList;

import java.awt.event.ActionEvent;

/**
 * Action to edit formulas in the actions mode
 * @author Alexander Weigl
 * @author Sarah Grebing
 * @version 2 (25.05.18)
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
        //enable only if position is in sequent
        setEnabled(!pis.isSequent());
    }

    /**
     *
     * If action is chosen in context menu
     * @param e
     */
    @Override
    public void actionPerformed(ActionEvent e) {
        if (posInSeq.isSequent()) return;

        TermBuilder tb = getMediator().getServices().getTermBuilder();
        PosInOccurrence pio = posInSeq.getPosInOccurrence();
        Term term = pio.subTerm();
        SequentFormula sf = pio.sequentFormula();
        Goal g = getMediator().getSelectedGoal();
        Term newTerm = promptForTerm(mainWindow, term);
        
        if (newTerm.equals(term)) {
            return;
        }

        TacletApp app;
        //  boolean isSoundMode = getMediator().getExplorationModeModel().getExplorationTacletAppState() == ExplorationModeModel.ExplorationState.SOUND_APPS;
        //if(isSoundMode){

        app = soundChange(pio, sf.formula(), tb.replace(sf.formula(), pio.posInTerm(), newTerm));


        //} else {
        //   app = changeFormula(pio, newTerm);

        //}

        g.node().getNodeInfo().register(new ExplorationNodeData(), ExplorationNodeData.class);
        g.node().getNodeInfo().get(ExplorationNodeData.class).setExplorationAction("Edit " + term + " to " + newTerm);

        ImmutableList<Goal> result = g.apply(app);
        result.forEach(goal -> {
            goal.node().getNodeInfo().register(new ExplorationNodeData(), ExplorationNodeData.class);
            String s = goal.node().getNodeInfo().getBranchLabel();
            goal.node().getNodeInfo().setBranchLabel("ExplorationNode: " + s);
        });

        //apply the weakening
        //if(isSoundMode){
        FindTaclet tap;

        boolean inAntec = posInSeq.getPosInOccurrence().isInAntec();
        if (inAntec) {
            tap = (FindTaclet) getMediator().getSelectedProof().getEnv().getInitConfigForEnvironment().lookupActiveTaclet(new Name("hide_left"));
        } else {
            tap = (FindTaclet) getMediator().getSelectedProof().getEnv().getInitConfigForEnvironment().lookupActiveTaclet(new Name("hide_right"));
        }


        TacletApp weakening = PosTacletApp.createPosTacletApp(tap, tap.getMatcher().matchFind(pio.subTerm(),
                MatchConditions.EMPTY_MATCHCONDITIONS,
                null), pio, getMediator().getServices());

        String posToWeakening = inAntec? "TRUE" : "FALSE";

        result.forEach(goal -> {

            if (goal.node().getNodeInfo().getBranchLabel().contains(posToWeakening)) {
                goal.apply(weakening);
                goal.node().parent().getNodeInfo().register(new ExplorationNodeData(), ExplorationNodeData.class);
            } else {
                goal.setEnabled(false);
            }
        });
    }

    private TacletApp soundChange(PosInOccurrence pio, Term term, Term newTerm) {
        Taclet cut = getMediator().getSelectedProof().getEnv().getInitConfigForEnvironment().lookupActiveTaclet(new Name("cut"));
        getMediator().getServices().getTermBuilder().equals(term, newTerm);
        Semisequent semisequent = new Semisequent(new SequentFormula(newTerm));

        TacletApp app = NoPosTacletApp.createNoPosTacletApp(cut);

        SchemaVariable sv = app.uninstantiatedVars().iterator().next();

        app = app.addCheckedInstantiation(sv, semisequent.getFirst().formula(), getMediator().getServices(), true);

        return app;
    }

    /*public TacletApp changeFormula(PosInOccurrence pos, Term replaceWith) {
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
    }*/
}
