/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;

import org.key_project.logic.Name;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.TermCreationException;
import org.key_project.logic.op.AbstractOperator;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableSet;


/**
 * This singleton class implements a general conditional operator
 * <tt>\if (phi) \then (t1) \else (t2)</tt>.
 */
public final class IfThenElse extends AbstractOperator implements Operator {

    public static final IfThenElse IF_THEN_ELSE = new IfThenElse();

    private IfThenElse() {
        super(new Name("if-then-else"), 3, true);
    }

    private Sort getCommonSuperSort(Sort s1, Sort s2) {
        if (s1 == JavaDLTheory.FORMULA) {
            assert s2 == JavaDLTheory.FORMULA : "Sorts FORMULA and " + s2 + " are incompatible.";
            return JavaDLTheory.FORMULA;
        } else if (s1.extendsTrans(s2)) {
            return s2;
        } else if (s2.extendsTrans(s1)) {
            return s1;
        } else if (s1 instanceof NullSort || s2 instanceof NullSort) {
            return JavaDLTheory.ANY;
        } else {
            Sort result = JavaDLTheory.ANY;
            final ImmutableSet<Sort> set1 = s1.extendsSorts();
            final ImmutableSet<Sort> set2 = s2.extendsSorts();
            assert set1 != null : "null for sort: " + s1;
            assert set2 != null : "null for sort: " + s2;

            for (final Sort sort1 : set1) {
                if (set2.contains(sort1)) {
                    if (result == JavaDLTheory.ANY) {
                        result = sort1;
                    } else {
                        // not uniquely determinable
                        return JavaDLTheory.ANY;
                    }
                }
            }

            return result;
        }
    }

    @Override
    public Sort sort(Sort[] sorts) {
        final Sort s2 = sorts[1];
        final Sort s3 = sorts[2];
        if (s2 instanceof ProgramSVSort || s2 == AbstractTermTransformer.METASORT) {
            return s3;
        } else if (s3 instanceof ProgramSVSort || s3 == AbstractTermTransformer.METASORT) {
            return s2;
        } else {
            return getCommonSuperSort(s2, s3);
        }
    }

    public <T extends org.key_project.logic.Term> void validTopLevelException(T term)
            throws TermCreationException {
        super.validTopLevelException(term);

        final Sort s0 = term.sub(0).sort();
        final Sort s1 = term.sub(1).sort();
        final Sort s2 = term.sub(2).sort();

        if (!(s0 == JavaDLTheory.FORMULA
                && (s1 == JavaDLTheory.FORMULA) == (s2 == JavaDLTheory.FORMULA)
                && s1 != JavaDLTheory.UPDATE && s2 != JavaDLTheory.UPDATE)) {
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
