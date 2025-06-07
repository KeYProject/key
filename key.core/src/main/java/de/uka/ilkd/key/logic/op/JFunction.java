/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.Sorted;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;

import org.key_project.logic.Name;
import org.key_project.logic.TermCreationException;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.Operator;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;


/**
 * Objects of this class represent function and predicate symbols in JavaDL. Note that program
 * variables are a
 * separate syntactic category, and not a type of function.
 * <br>
 * <strong>As soon as {@link AbstractTermTransformer#METASORT} is generalized, this class
 * may be deleted.</strong>
 */
public class JFunction extends Function implements Sorted, Operator {


    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    JFunction(Name name, Sort sort, ImmutableArray<Sort> argSorts,
            ImmutableArray<Boolean> whereToBind, boolean unique, boolean isRigid,
            boolean isSkolemConstant) {
        super(name, argSorts, sort, whereToBind, isRigid, unique, isSkolemConstant);

        assert sort != JavaDLTheory.UPDATE;
        assert !(unique && sort == JavaDLTheory.FORMULA);
        assert !(sort instanceof NullSort) || name.toString().equals("null")
                : "Functions with sort \"null\" are not allowed: " + this;
    }

    public JFunction(Name name, Sort sort, ImmutableArray<Sort> argSorts,
            ImmutableArray<Boolean> whereToBind, boolean unique) {
        this(name, sort, argSorts, whereToBind, unique, true, false);
    }

    public JFunction(Name name, Sort sort, ImmutableArray<Sort> argSorts,
            ImmutableArray<Boolean> whereToBind, boolean unique, boolean isSkolemConstant) {
        this(name, sort, argSorts, whereToBind, unique, true, isSkolemConstant);
    }

    public JFunction(Name name, Sort sort, Sort[] argSorts, Boolean[] whereToBind,
            boolean unique) {
        this(name, sort, new ImmutableArray<>(argSorts),
            whereToBind == null ? null : new ImmutableArray<>(whereToBind), unique);
    }

    public JFunction(Name name, Sort sort, Sort[] argSorts, Boolean[] whereToBind,
            boolean unique,
            boolean isSkolemConstant) {
        this(name, sort, new ImmutableArray<>(argSorts),
            whereToBind == null ? null : new ImmutableArray<>(whereToBind), unique,
            isSkolemConstant);
    }

    JFunction(Name name, Sort sort, ImmutableArray<Sort> argSorts, boolean isRigid) {
        this(name, sort, argSorts, null, false, isRigid, false);
    }

    public JFunction(Name name, Sort sort, ImmutableArray<Sort> argSorts) {
        this(name, sort, argSorts, null, false);
    }

    public JFunction(Name name, Sort sort, Sort... argSorts) {
        this(name, sort, argSorts, null, false);
    }

    public JFunction(Name name, Sort sort, boolean isSkolemConstant, Sort... argSorts) {
        this(name, sort, argSorts, null, false, isSkolemConstant);
    }

    public JFunction(Name name, Sort sort) {
        this(name, sort, new ImmutableArray<>(), null, false);
    }

    public JFunction(Name name, Sort sort, boolean isSkolemConstant) {
        this(name, sort, new ImmutableArray<>(), null, false, true, isSkolemConstant);
    }

    /**
     * checks if a given Term could be subterm (at the at'th subterm position) of a term with this
     * function at its top level. The validity of the given subterm is NOT checked.
     *
     * @param at the position of the term where this method should check the validity.
     * @param possibleSub the subterm to be checked.
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
