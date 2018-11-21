package de.uka.ilkd.key.gui.actions.exploration;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.proofExploration.ExplorationModeModel;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.TacletApp;
import org.key_project.util.collection.ImmutableList;

import java.awt.event.ActionEvent;

/**
 * Action for the user to visually delete formulas from the sequent (using hide)
 */
public class DeleteFormulaAction extends ExplorationAction {

    private final PosInSequent posInSeq;

    public DeleteFormulaAction(PosInSequent pis) {
        this(pis, MainWindow.getInstance());
    }

    public DeleteFormulaAction(PosInSequent pis, MainWindow mainWindow) {
        super(mainWindow);
        setName("Delete formula");
        this.posInSeq = pis;
        //only enable if position is in sequent and a toplevel formula
        if(pis.getPosInOccurrence() != null) {
            setEnabled(!pis.isSequent() & pis.getPosInOccurrence().isTopLevel());
        } else {
            setEnabled(false);
        }
    }


    @Override
    public void actionPerformed(ActionEvent e) {
        if (posInSeq.isSequent() || (posInSeq.getPosInOccurrence() != null && !posInSeq.getPosInOccurrence().isTopLevel())) return;


        PosInOccurrence pio = posInSeq.getPosInOccurrence();
        Term term = pio.subTerm();
        Goal g = getMediator().getSelectedGoal();
        g.node().getNodeInfo().setExploration(true);

        TacletApp app;
        //boolean isSoundMode = getMediator().getExplorationModeModel().getExplorationTacletAppState() == ExplorationModeModel.ExplorationState.WHOLE_APP;
        app = soundWeakening(pio, term);
        ImmutableList<Goal> result = g.apply(app);
        result.forEach(goal -> {
            //goal.node().getNodeInfo().setExploration(true);
            goal.node().getNodeInfo().setExplorationAction("Hide "+term);

        });
    }

    private TacletApp soundWeakening(PosInOccurrence pio, Term term) {
        FindTaclet tap;
        if(posInSeq.getPosInOccurrence().isInAntec()){
            tap = (FindTaclet) getMediator().getSelectedProof().getEnv().getInitConfigForEnvironment().lookupActiveTaclet(new Name("hide_left"));
        } else {
            tap = (FindTaclet) getMediator().getSelectedProof().getEnv().getInitConfigForEnvironment().lookupActiveTaclet(new Name("hide_right"));
        }

        TacletApp weakening = PosTacletApp.createPosTacletApp(tap, tap.getMatcher().matchFind(pio.subTerm(),
                MatchConditions.EMPTY_MATCHCONDITIONS,
                null), pio, getMediator().getServices());
        return weakening;
    }

}
