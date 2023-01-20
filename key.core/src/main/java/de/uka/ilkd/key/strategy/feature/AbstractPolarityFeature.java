package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;


/**
 * Auxiliary class that contains methods to compute the polarity of a position/subformula within a
 * formula
 */
public abstract class AbstractPolarityFeature {

    /**
     * @param formulaPol the polarity of the complete formula (i.e. whether the formula is part of
     *        antecedent or succedent, <code>Boolean.TRUE</code> for antecedent)
     * @return the polarity of the given position, which is
     *         <code>Boolean.TRUE</code>,<code>Boolean.FALSE</code> or <code>null</code>
     */
    protected Boolean polarity(PosInOccurrence pos, Boolean formulaPol) {
        if (formulaPol == null)
            return null;

        final PIOPathIterator it = pos.iterator();

        while (it.next() != -1) {
            final Term t = it.getSubTerm();
            final Operator op = t.op();

            if (op == Junctor.NOT || op == Junctor.IMP && it.getChild() == 0)
                formulaPol = invert(formulaPol);
            else if (op == Equality.EQV || (op == IfThenElse.IF_THEN_ELSE && it.getChild() == 0))
                return null;
        }

        return formulaPol;
    }

    private Boolean invert(Boolean p) {
        return p == null ? null : (p.booleanValue() ? Boolean.FALSE : Boolean.TRUE);
    }

}
