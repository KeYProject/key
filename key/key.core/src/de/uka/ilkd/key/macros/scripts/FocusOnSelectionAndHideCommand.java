package de.uka.ilkd.key.macros.scripts;

import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.macros.scripts.meta.Option;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import java.util.Iterator;
import java.util.Set;

/**
 * Hide all formulas that are not selected
 * Parameter:
 * * The sequent with those formulas that should not be hidden
 * Created by sarah on 1/12/17.
 */
public class FocusOnSelectionAndHideCommand
        extends AbstractCommand<FocusOnSelectionAndHideCommand.Parameters> {

    public FocusOnSelectionAndHideCommand() {
        super(Parameters.class);
    }

    static class Parameters {
        @Option("#2") public Sequent toKeep;
    }

    @Override public void execute(Parameters s)
            throws ScriptException, InterruptedException {
        if (s == null) {
            throw new ScriptException("Missing 'sequent' argument for focus");
        }

        Sequent toKeep = s.toKeep;

        //toKeep = parseSequent(sequentString, getGoalFromCurrentState());
        try {
            hideAll(toKeep);
        }
        catch (ParserException e) {
            e.printStackTrace();
        }

    }

    @Override public String getName() {
        return "focus";
    }

    /*
    private Goal getGoalFromCurrentState() {
        Object fixedGoal = stateMap.get(GOAL_KEY);
        if (fixedGoal instanceof Node) {
            Node fixed = (Node) fixedGoal;
            //case node is already modified by focus, the child has to be returned
            if (!fixed.leaf()) {
                assert fixed.childrenCount() == 1;
                fixed = fixed.child(0);
            }
            Goal g = state.getGoal(proof.openGoals(), fixed);
            return g;
        }
        return null;
    }
    */

    /**
     * Hide all formulas of the sequent that are not focus sequent
     *
     * @param toKeep
     * @throws ParserException
     * @throws ScriptException
     */
    private void hideAll(Sequent toKeep)
            throws ParserException, ScriptException {
        while (true) {
            //get current goal
            Goal g = state.getFirstOpenAutomaticGoal();
            //find formulas that should be hidden in sequent of current goal

            //hide

            if (g != null) {

                SequentFormula toHide = iterateThroughSequentAndFindNonMatch(g,
                        toKeep);
                //as long as there is a match
                if (toHide != null) {
                    boolean antec = false;

                    Taclet tac;
                    if (g.sequent().antecedent().contains(toHide)) {
                        tac = getTaclet(toHide.formula(), "left");
                        antec = true;

                    }
                    else {
                        tac = getTaclet(toHide.formula(), "right");

                    }
                    makeTacletApp(g, toHide, tac, antec);

                }
                else {
                    //no formulas to hide any more on sequent
                    break;
                }

            }
            else {
                //goal is null
                break;
            }
        }

    }

    //determine where formula in sequent and apply either hide_left or hide_right
    private Taclet getTaclet(Term t, String pos) throws ScriptException {
        String ruleName;
        Taclet tac;
        switch (pos) {
        case "left":
            ruleName = "hide_left";
            break;
        case "right":
            ruleName = "hide_right";
            break;
        default:
            ruleName = "";
            throw new ScriptException(
                    "Position of term " + t.toString() + "unknown");
        }

        tac = proof.getEnv().getInitConfigForEnvironment()
                .lookupActiveTaclet(new Name(ruleName));

        return tac;

    }

    /**
     * Iterate through sequent and find first formula that is not in the list of formulas to keep and return this formula
     *
     * @param g
     * @param toKeep
     * @return formula to hide, if all formulas in the sequent should be kept, returns null
     * @throws ScriptException
     * @throws ParserException
     */

    private SequentFormula iterateThroughSequentAndFindNonMatch(Goal g,
            Sequent toKeep) throws ScriptException, ParserException {
        Semisequent focusedAntec = toKeep.antecedent();
        Semisequent focusedSucc = toKeep.succedent();

        Sequent currentGoalSeq = g.sequent();
        Semisequent currentAntec = currentGoalSeq.antecedent();
        Semisequent currentSucc = currentGoalSeq.succedent();

        //first iterate through antecedent
        Iterator<SequentFormula> iterator = currentAntec.iterator();
        while (iterator.hasNext()) {
            SequentFormula form = iterator.next();
            Iterator<SequentFormula> focusAntecIter = focusedAntec.iterator();

            Boolean isIn = false;
            while (focusAntecIter.hasNext()) {
                SequentFormula toKeepForm = focusAntecIter.next();
                if (toKeepForm.equals(form)) {
                    isIn = true;
                    break;
                }
            }

/*                if(form.formula().equalsModRenaming(t) ){
                    isIn = true;
                }*/

            if (!isIn) {
                return form;
            }
        }
        //if in antecedent no formula to hide iterate through succedent
        Iterator<SequentFormula> iteratorSucc = currentSucc.iterator();

        while (iteratorSucc.hasNext()) {
            Boolean isIn = false;
            SequentFormula form = iteratorSucc.next();
            Iterator<SequentFormula> focusSuccIter = focusedSucc.iterator();

            while (focusSuccIter.hasNext()) {
                SequentFormula toKeepForm = focusSuccIter.next();
                if (toKeepForm.equals(form)) {
                    isIn = true;
                    break;
                }
            }
            if (!isIn) {
                return form;
            }
        }
        //if no formulas to hide, return null
        return null;
    }

    /**
     * Make tacletApp for one sequent formula to hide on the sequent
     *
     * @param g      the goal on which this hide rule should be applied to
     * @param toHide the sequent formula to hide
     * @param tac    the taclet top apply (either hide_left or hide_right)
     * @param antec  whether the formula is in the antecedent
     * @throws ScriptException
     */
    private void makeTacletApp(Goal g, SequentFormula toHide, Taclet tac,
            boolean antec) throws ScriptException {

        //hide rules only applicable to top-level terms/sequent formulas
        PosInTerm pit = PosInTerm.getTopLevel();

        PosInOccurrence pio = new PosInOccurrence(toHide, pit, antec);

        Set<SchemaVariable> svs = tac.collectSchemaVars();
        assert svs.size() == 1;
        Iterator<SchemaVariable> iter = svs.iterator();
        SchemaVariable sv = (SchemaVariable) iter.next();

        SVInstantiations inst = SVInstantiations.EMPTY_SVINSTANTIATIONS;

        TacletApp app = PosTacletApp
                .createPosTacletApp((FindTaclet) tac, inst, pio,
                        proof.getServices());
        app = app.addCheckedInstantiation(sv, toHide.formula(),
                proof.getServices(), true);
        g.apply(app);

    }

}

