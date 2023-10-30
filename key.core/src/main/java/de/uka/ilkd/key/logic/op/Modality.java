/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermCreationException;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.logic.sort.Sort;

import org.key_project.logic.Name;
import org.key_project.logic.Program;

/**
 * This class is used to represent a dynamic logic modality like diamond and box (but also
 * extensions of DL like preserves and throughout are possible in the future).
 */
public class Modality extends org.key_project.logic.op.Modality<Sort> implements Operator {
    /**
     * Creates a modal operator with the given name
     * <strong>Creation must only be done by {@link de.uka.ilkd.key.logic.TermServices}!</strong>
     *
     */
    public Modality(Program prg, JavaModalityKind kind) {
        super(kind.name(), JavaDLTheory.FORMULA, prg, kind);
    }

    @Override
    public JavaBlock program() {
        return (JavaBlock) super.program();
    }

    /**
     * Whether this is a transaction modality
     */
    public boolean transaction() {
        return this.<JavaModalityKind>kind().transaction();
    }

    /**
     * checks if a given Term could be subterm (at the at'th subterm position) of a term with this
     * function at its top level. The validity of the given subterm is NOT checked.
     *
     * @param at the position of the term where this method should check the validity.
     * @param possibleSub the subterm to be checked.
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


    protected final void additionalValidTopLevel(Term term) {
        for (int i = 0, n = arity(); i < n; i++) {
            if (!possibleSub(i, term.sub(i))) {
                throw new TermCreationException(this, term);
            }
        }
    }

    @Override
    public void validTopLevelException(Term term) throws TermCreationException {
        if (1 != term.arity()) {
            throw new TermCreationException(this, term);
        }

        if (1 != term.subs().size()) {
            throw new TermCreationException(this, term);
        }

        if (!term.boundVars().isEmpty()) {
            throw new TermCreationException(this, term);
        }

        for (int i = 0; i < 1; i++) {
            if (term.sub(i) == null) {
                throw new TermCreationException(this, term);
            }
        }

        additionalValidTopLevel(term);
    }

    @Override
    public String toString() {
        if (kind() instanceof ModalOperatorSV) {
            return kind().toString();
        }
        return super.toString();
    }

    public static class JavaModalityKind extends Kind implements SVSubstitute {
        private static final Map<String, JavaModalityKind> kinds = new HashMap<>();
        /**
         * The diamond operator of dynamic logic. A formula <alpha;>Phi can be read as after
         * processing
         * the program alpha there exists a state such that Phi holds.
         */
        public static final JavaModalityKind DIA = new JavaModalityKind(new Name("diamond"));
        /**
         * The box operator of dynamic logic. A formula [alpha;]Phi can be read as 'In all states
         * reachable processing the program alpha the formula Phi holds'.
         */
        public static final JavaModalityKind BOX = new JavaModalityKind(new Name("box"));
        /**
         * A Java Card transaction version of the diamond modality. Means that a transaction is
         * currently underway.
         */
        public static final JavaModalityKind DIA_TRANSACTION =
            new JavaModalityKind(new Name("diamond_transaction"));
        /**
         * A Java Card transaction version of the box modality. Means that a transaction is
         * currently
         * underway.
         */
        public static final JavaModalityKind BOX_TRANSACTION =
            new JavaModalityKind(new Name("box_transaction"));
        /**
         * The throughout operator of dynamic logic. A formula [[alpha;]]Phi can be read as during
         * processing the program alpha Phi should hold at every step of execution.
         */
        public static final JavaModalityKind TOUT = new JavaModalityKind(new Name("throughout"));
        /**
         * A Java Card transaction version of the throughout modality. Means that a transaction is
         * currently underway.
         */
        public static final JavaModalityKind TOUT_TRANSACTION =
            new JavaModalityKind(new Name("throughout_transaction"));

        public JavaModalityKind(Name name) {
            super(name);
            kinds.put(name.toString(), this);
        }

        public static JavaModalityKind getKind(String name) {
            return kinds.get(name);
        }

        /**
         * Whether this modality is termination sensitive, i.e., it is a "diamond-kind" modality.
         */
        public boolean terminationSensitive() {
            return (this == DIA || this == DIA_TRANSACTION);
        }

        /**
         * Whether this is a transaction modality
         */
        public boolean transaction() {
            return (this == BOX_TRANSACTION || this == DIA_TRANSACTION);
        }
    }
}
