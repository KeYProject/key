// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 

package de.uka.ilkd.key.gui.macros;

import java.awt.event.InputEvent;
import java.awt.event.KeyEvent;

import javax.swing.KeyStroke;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.Strategy;

/**
 * The macro applies only symbolic execution and update rules.
 * This is in contrast to FinishSymbolicExecution, which applies <i>any</i>
 * rule as long as there is a modality on the sequent.
 * @author bruns
 */
public class SymbolicExecutionMacro extends StrategyProofMacro {

    @Override
    public String getName() {
        return "Finish Symbolic Execution (SymEx only)";
    }

    @Override
    public String getDescription() {
        return "Symbolically execute programs (including update simplification).";
    }

    /*
     * find a modality term in a node
     */
    private static boolean hasModality(Node node) {
        Sequent sequent = node.sequent();
        for (SequentFormula sequentFormula : sequent) {
            if(getNextModality(sequentFormula.formula()) != null) {
                return true;
            }
        }

        return false;
    }

    /**
     * Recursively descent into the term to find a modality term.
     * Return null if none found.
     */
    private static Term getNextModality(Term term) {
        if(term.op() instanceof Modality) {
            return term;
        }

        for (Term sub : term.subs()) {
            final Term nextMod = getNextModality(sub);
            if (nextMod != null) return nextMod;
        }

        return null;
    }

    @Override
    protected Strategy createStrategy(KeYMediator mediator, PosInOccurrence posInOcc) {
        return new FilterSymbexStrict(
                mediator.getInteractiveProver().getProof().getActiveStrategy());
    }

    @Override
    public KeyStroke getKeyStroke () {
	return KeyStroke.getKeyStroke(KeyEvent.VK_X, InputEvent.SHIFT_DOWN_MASK);
    }

    private static class FilterSymbexStrict extends FilterStrategy {

        private static final Name NAME = new Name(FilterSymbexStrict.class.getSimpleName());

        public FilterSymbexStrict(Strategy delegate) {
            super(delegate);
        }

        @Override
        public Name name() {
            return NAME;
        }

        @Override
        public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
            if(!hasModality(goal.node())) {
                return false;
            }
            if (pio == null || pio.subTerm() == null) return false;
            final Operator target = pio.subTerm().op();
            
            if (target instanceof Modality || target instanceof UpdateApplication)
                return super.isApprovedApp(app, pio, goal);
            else return false;
        }

    }

}
