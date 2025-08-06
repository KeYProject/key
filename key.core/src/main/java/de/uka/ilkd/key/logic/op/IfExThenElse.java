/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.ldt.JavaDLTheory;

import org.key_project.logic.Name;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.Term;
import org.key_project.logic.TermCreationException;
import org.key_project.logic.op.AbstractOperator;
import org.key_project.logic.op.Operator;
import org.key_project.logic.sort.Sort;


/**
 * This singleton class implements a conditional operator "\ifEx iv; (phi) \then (t1) \else (t2)",
 * where iv is an integer logic variable, phi is a formula, and where t1 and t2 are terms with the
 * same sort. The variable iv is bound in phi and in t1, but not in t2.
 */
public final class IfExThenElse extends AbstractOperator implements Operator {

    public static final IfExThenElse IF_EX_THEN_ELSE = new IfExThenElse();


    private IfExThenElse() {
        super(new Name("ifExThenElse"), 3, new Boolean[] { true, true, false }, true);
    }


    @Override
    public Sort sort(Sort[] sorts) {
        return sorts[1];
    }


    @Override
    public <T extends Term> void validTopLevelException(T term)
            throws TermCreationException {
        super.validTopLevelException(term);
        final Sort s0 = term.sub(0).sort();
        final Sort s1 = term.sub(1).sort();
        final Sort s2 = term.sub(2).sort();

        if (!(s0 == JavaDLTheory.FORMULA && s1.equals(s2))) {
            throw new TermCreationException(this, term);
        }
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public SyntaxElement getChild(int n) {
        throw new IndexOutOfBoundsException(name() + " has no children");
    }
}
