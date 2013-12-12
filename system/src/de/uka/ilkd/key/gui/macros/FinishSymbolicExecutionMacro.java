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
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.Strategy;

/**
 * The macro FinishSymbolicExecutionMacro continues automatic rule application
 * until there is no more modality on the sequent.
 *
 * This is done by implementing a delegation {@link Strategy} which assigns to
 * any rule application infinite costs if there is no modality on the sequent.
 *
 * @author mattias ulbrich
 */
public class FinishSymbolicExecutionMacro extends StrategyProofMacro {

    @Override
    public String getName() {
        return "Finish symbolic execution";
    }

    @Override
    public String getDescription() {
        return "Continue automatic strategy application until no more modality is on the sequent.";
    }

    /*
     * find a modality term in a node
     */
    private static boolean hasModality(Node node) {
        Sequent sequent = node.sequent();
        for (SequentFormula sequentFormula : sequent) {
            if(hasModality(sequentFormula.formula())) {
                return true;
            }
        }

        return false;
    }

    /*
     * recursively descent into the term to detect a modality.
     */
    private static boolean hasModality(Term term) {
        if(term.op() instanceof Modality) {
            return true;
        }

        for (Term sub : term.subs()) {
            if(hasModality(sub)) {
                return true;
            }
        }

        return false;
    }

    @Override
    protected Strategy createStrategy(KeYMediator mediator, PosInOccurrence posInOcc) {
        return new FilterSymbexStrategy(
                mediator.getInteractiveProver().getProof().getActiveStrategy());
    }

    @Override
    public KeyStroke getKeyStroke () {
	return KeyStroke.getKeyStroke(KeyEvent.VK_X, InputEvent.SHIFT_DOWN_MASK);
    }

    /**
     * The Class FilterAppManager is a special strategy assigning to any rule
     * infinite costs if the goal has no modality
     */
    private static class FilterSymbexStrategy extends FilterStrategy {

        private static final Name NAME = new Name(FilterSymbexStrategy.class.getSimpleName());

        public FilterSymbexStrategy(Strategy delegate) {
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

            return super.isApprovedApp(app, pio, goal);
        }

    }

}
