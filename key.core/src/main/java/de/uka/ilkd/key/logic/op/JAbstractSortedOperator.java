/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.Sorted;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;

import org.key_project.logic.Name;
import org.key_project.logic.TermCreationException;
import org.key_project.logic.op.AbstractSortedOperator;
import org.key_project.logic.op.Modifier;
import org.key_project.logic.op.Operator;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;


/**
 * Abstract sorted operator class offering some common functionality.
 */
public abstract class JAbstractSortedOperator extends AbstractSortedOperator
        implements Sorted, Operator {

    protected JAbstractSortedOperator(Name name, ImmutableArray<Sort> argSorts, Sort sort,
            ImmutableArray<Boolean> whereToBind, Modifier modifier) {
        super(name, argSorts, sort, whereToBind, modifier);
    }

    protected JAbstractSortedOperator(Name name, ImmutableArray<Sort> argSorts, Sort sort,
            ImmutableArray<Boolean> whereToBind, boolean isRigid) {
        this(name, argSorts, sort, whereToBind, isRigid ? Modifier.RIGID : Modifier.NONE);
    }

    protected JAbstractSortedOperator(Name name, Sort[] argSorts, Sort sort, Boolean[] whereToBind,
            boolean isRigid) {
        this(name, new ImmutableArray<>(argSorts), sort,
            new ImmutableArray<>(whereToBind), isRigid);
    }

    protected JAbstractSortedOperator(Name name, ImmutableArray<Sort> argSorts, Sort sort,
            boolean isRigid) {
        this(name, argSorts, sort, null, isRigid);
    }

    protected JAbstractSortedOperator(Name name, Sort[] argSorts, Sort sort, boolean isRigid) {
        this(name, new ImmutableArray<>(argSorts), sort, null, isRigid);
    }

    protected JAbstractSortedOperator(Name name, Sort sort, boolean isRigid) {
        this(name, new ImmutableArray<>(), sort, null, isRigid);
    }

    /**
     * checks if a given Term could be subterm (at the at'th subterm position) of a term with this
     * function at its top level. The validity of the given subterm is NOT checked.
     *
     * @param at theposition of the term where this method should check the validity.
     * @param possibleSub the subterm to be ckecked.
     * @return true iff the given term can be subterm at the indicated position
     */
    private boolean possibleSub(int at, JTerm possibleSub) {
        final Sort s = possibleSub.sort();

        return s == AbstractTermTransformer.METASORT || s instanceof ProgramSVSort
                || argSort(at) == AbstractTermTransformer.METASORT
                || argSort(at) instanceof ProgramSVSort || s.extendsTrans(argSort(at));
    }


    /*
     * weigl: disable this method, not used. You should use inheritance!
     *
     * Allows subclasses to impose custom demands on what constitutes a valid term using the
     * operator represented by the subclass. The default implementation here does not impose any
     * such demands. protected boolean additionalValidTopLevel2(Term term) { return true; }
     */
    @Override
    public <T extends org.key_project.logic.Term> void validTopLevelException(T term)
            throws TermCreationException {
        super.validTopLevelException(term);
        for (int i = 0, n = arity(); i < n; i++) {
            if (!possibleSub(i, (JTerm) term.sub(i))) {
                throw new TermCreationException(this, term);
            }
        }
    }
}
