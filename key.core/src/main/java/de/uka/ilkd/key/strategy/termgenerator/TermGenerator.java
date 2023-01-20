package de.uka.ilkd.key.strategy.termgenerator;

import java.util.Iterator;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;


/**
 * Interface for objects that generate lists/sequences of terms or formulas. This interface is used
 * in the feature <code>ForEachCP</code> in order to instantiate schema variables with different
 * terms/formulas.
 */
public interface TermGenerator {
    Iterator<Term> generate(RuleApp app, PosInOccurrence pos, Goal goal);
}
