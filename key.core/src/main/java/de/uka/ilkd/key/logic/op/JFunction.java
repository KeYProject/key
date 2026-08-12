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

import static org.key_project.logic.op.Function.FunctionKind.ORDINARY;


/**
 * Objects of this class represent function and predicate symbols in JavaDL. Note that program
 * variables are a separate syntactic category, and not a type of function.
 * <br>
 * <strong>As soon as {@link AbstractTermTransformer#METASORT} is generalized, this class
 * may be deleted.</strong>
 */
public class JFunction extends Function implements Sorted, Operator {

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    /**
     * Creates a function symbol with the specified signature and kind
     *
     * @param name the Name of the function symbol
     * @param sort the Sort of the function symbol
     * @param argSorts the Sorts of its parameters
     * @param whereToBind if it is a binder the position where the bound variable is in scope (can
     *        be used)
     * @param unique a boolean indicating whether the symbol is unique
     * @param kind the kind of the function symbol
     * @param isRigid a boolean specifying whether the symbol is state depending (i.e., can have
     *        different values
     *        in different states)
     * @param introductionTime the introduction time of the symbol, or a
     *        {@link Function#UNRECORDED}, if none available (e.g. existed from the beginning)
     */
    JFunction(Name name, Sort sort, ImmutableArray<Sort> argSorts,
            ImmutableArray<Boolean> whereToBind, boolean unique, boolean isRigid,
            FunctionKind kind, int introductionTime) {
        super(name, argSorts, sort, whereToBind, isRigid, unique, kind, introductionTime);

        assert sort != JavaDLTheory.UPDATE;
        assert !(unique && sort == JavaDLTheory.FORMULA);
        assert !(sort instanceof NullSort) || name.toString().equals("null")
                : "Functions with sort \"null\" are not allowed: " + this;
    }

    public JFunction(Name name, Sort sort, ImmutableArray<Sort> argSorts,
            ImmutableArray<Boolean> whereToBind, boolean unique) {
        this(name, sort, argSorts, whereToBind, unique, true, ORDINARY, UNRECORDED);
    }

    /**
     * Creates a function symbol with the specified signature and kind
     *
     * @param name the Name of the function symbol
     * @param sort the Sort of the function symbol
     * @param argSorts the Sorts of its parameters
     * @param whereToBind if it is a binder the position where the bound variable is in scope (can
     *        be used)
     * @param unique a boolean indicating whether the symbol is unique
     * @param kind the kind of the function symbol
     * @param introductionTime the introduction time of the symbol, or a
     *        {@link Function#UNRECORDED}, if none available (e.g. existed from the beginning)
     */
    public JFunction(Name name, Sort sort, ImmutableArray<Sort> argSorts,
            ImmutableArray<Boolean> whereToBind, boolean unique, FunctionKind kind,
            int introductionTime) {
        this(name, sort, argSorts, whereToBind, unique, true, kind, introductionTime);
    }

    public JFunction(Name name, Sort sort, Sort[] argSorts, Boolean[] whereToBind,
            boolean unique) {
        this(name, sort, new ImmutableArray<>(argSorts),
            whereToBind == null ? null : new ImmutableArray<>(whereToBind), unique);
    }

    JFunction(Name name, Sort sort, ImmutableArray<Sort> argSorts, boolean isRigid) {
        this(name, sort, argSorts, null, false, isRigid, ORDINARY, UNRECORDED);
    }

    public JFunction(Name name, Sort sort, ImmutableArray<Sort> argSorts) {
        this(name, sort, argSorts, null, false);
    }

    public JFunction(Name name, Sort sort, Sort... argSorts) {
        this(name, sort, argSorts, null, false);
    }

    public JFunction(Name name, Sort sort) {
        this(name, sort, new ImmutableArray<>(), null, false);
    }

    /**
     * Creates a constant of the given kind
     */
    public JFunction(Name name, Sort sort, FunctionKind kind) {
        this(name, sort, new ImmutableArray<>(), null, false, true, kind, UNRECORDED);
    }

    public JFunction(Name name, Sort sort, FunctionKind kind, int introductionTime) {
        this(name, sort, new ImmutableArray<>(), null, false, true, kind, introductionTime);
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
