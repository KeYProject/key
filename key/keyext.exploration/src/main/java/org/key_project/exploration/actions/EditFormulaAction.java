package org.key_project.exploration.actions;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.*;
import org.key_project.exploration.ExplorationNodeData;
import org.key_project.exploration.ProofExplorationService;
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

        ProofExplorationService api = ProofExplorationService.get(getMediator());
        Node toBeSelected = api.applyChangeFormula(g, pio, sf.formula(),
                tb.replace(sf.formula(), pio.posInTerm(), newTerm));
        getMediator().getSelectionModel().setSelectedNode(toBeSelected);
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
