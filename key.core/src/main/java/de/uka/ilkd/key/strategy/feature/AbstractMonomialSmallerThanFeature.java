/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.ldt.IntegerLDT;

import org.key_project.logic.Term;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.Operator;
import org.key_project.util.collection.ImmutableList;

public abstract class AbstractMonomialSmallerThanFeature extends SmallerThanFeature {

    private final Function mul;

    protected AbstractMonomialSmallerThanFeature(IntegerLDT numbers) {
        this.mul = numbers.getMul();
    }

    /**
     * The point at which the definitional skolem symbol {@code op} was introduced, counted in
     * the rule applications its goal had seen, or -1 for every other operator. Such a symbol
     * abbreviates a term through a defining equation ({@code \skolemTerm[definitional]}), and
     * the ordering places it below all symbols that existed when it was made, newest lowest, so
     * that applying a definition is a decrease, also in chains of definitions. Kind and time are
     * constants of the symbol, which makes features built on this {@code StableCost}.
     *
     * @param op the Operator whose introduction time is queried
     * @return the introduction time, or -1 for an operator that is no definitional symbol
     */
    protected int introductionTime(Operator op) {
        if (op instanceof Function func && func.isDefinitionalSkolem()) {
            final int time = func.introductionTime();
            return time < 0 ? -1 : time;
        }
        return -1;
    }

    protected ImmutableList<Term> collectAtoms(Term t) {
        final AtomCollector m = new AtomCollector();
        m.collect(t);
        return m.getResult();
    }

    private class AtomCollector extends Collector {
        protected void collect(Term te) {
            if (te.op() == mul) {
                collect(te.sub(0));
                collect(te.sub(1));
            } else {
                addTerm(te);
            }
        }
    }
}
