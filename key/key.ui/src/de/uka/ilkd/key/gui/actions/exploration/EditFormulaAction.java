package de.uka.ilkd.key.gui.actions.exploration;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import java.awt.event.ActionEvent;
import java.util.Iterator;
import java.util.Set;

/**
 * @author Alexander Weigl
 * @version 1 (24.05.18)
 */
public class EditFormulaAction extends MainWindowAction {
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

        Term newTerm = AddFormulaToAntecedentAction.promptForTerm(mainWindow,
                LogicPrinter.quickPrintTerm(term, getMediator().getServices()));

        if (newTerm == null) {
            return;
        }

        TacletApp app = changeFormula(pio, newTerm);
        ImmutableList<Goal> result = g.apply(app);
        result.forEach(goal -> goal.node().getNodeInfo().setExploration(true));
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
