/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Sorted;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermCreationException;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.logic.sort.Sort;

import org.key_project.util.collection.ImmutableArray;


/**
 * Abstract sorted operator class offering some common functionality.
 */
public abstract class AbstractSortedOperator extends AbstractOperator
        implements SortedOperator, Sorted {

    private static final ImmutableArray<Sort> EMPTY_SORT_LIST = new ImmutableArray<>();

    private final Sort sort;
    private final ImmutableArray<Sort> argSorts;


    protected AbstractSortedOperator(Name name, ImmutableArray<Sort> argSorts, Sort sort,
            ImmutableArray<Boolean> whereToBind, boolean isRigid) {
        super(name, argSorts == null ? 0 : argSorts.size(), whereToBind, isRigid);
        if (sort == null) {
            throw new NullPointerException("Given sort is null");
        }
        this.argSorts = argSorts == null ? EMPTY_SORT_LIST : argSorts;
        this.sort = sort;
    }


    protected AbstractSortedOperator(Name name, Sort[] argSorts, Sort sort, Boolean[] whereToBind,
            boolean isRigid) {
        this(name, new ImmutableArray<>(argSorts), sort,
            new ImmutableArray<>(whereToBind), isRigid);
    }


    protected AbstractSortedOperator(Name name, ImmutableArray<Sort> argSorts, Sort sort,
            boolean isRigid) {
        this(name, argSorts, sort, null, isRigid);
    }


    protected AbstractSortedOperator(Name name, Sort[] argSorts, Sort sort, boolean isRigid) {
        this(name, new ImmutableArray<>(argSorts), sort, null, isRigid);
    }


    protected AbstractSortedOperator(Name name, Sort sort, boolean isRigid) {
        this(name, (ImmutableArray<Sort>) null, sort, null, isRigid);
    }


    @Override
    public final Sort sort(ImmutableArray<Term> terms) {
        return sort;
    }


    /**
     * checks if a given Term could be subterm (at the at'th subterm position) of a term with this
     * function at its top level. The validity of the given subterm is NOT checked.
     *
     * @param at theposition of the term where this method should check the validity.
     * @param possibleSub the subterm to be ckecked.
     * @return true iff the given term can be subterm at the indicated position
     */
    private boolean possibleSub(int at, Term possibleSub) {
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
    protected final void additionalValidTopLevel(Term term) {
        for (int i = 0, n = arity(); i < n; i++) {
            if (!possibleSub(i, term.sub(i))) {
                throw new TermCreationException(this, term);
            }
        }
    }


    @Override
    public final Sort argSort(int i) {
        return argSorts.get(i);
    }


    @Override
    public final ImmutableArray<Sort> argSorts() {
        return argSorts;
    }


    @Override
    public final Sort sort() {
        return sort;
    }
}
