/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import java.util.HashMap;
import java.util.Map;
import java.util.WeakHashMap;

import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;

import org.key_project.logic.Name;
import org.key_project.logic.TermCreationException;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.Pair;

/**
 * This class is used to represent a dynamic logic modality like diamond and box (but also
 * extensions of DL like preserves and throughout are possible in the future).
 */
public class Modality extends org.key_project.logic.op.Modality implements Operator {
    /**
     * keeps track of created modalities
     */
    private static final Map<Pair<JavaModalityKind, JavaProgramElement>, Modality> modalities =
        new WeakHashMap<>();

    /**
     * Retrieves the modality of the given kind and program.
     *
     * @param kind the kind of the modality such as diamond or box
     * @param jb the program of this modality
     * @return the modality of the given kind and program.
     */
    public static Modality getModality(Modality.JavaModalityKind kind, JavaBlock jb) {
        var pair = new Pair<>(kind, jb.program());
        Modality mod = modalities.get(pair);
        if (mod == null) {
            mod = new Modality(jb, kind);
            modalities.put(pair, mod);
        }
        return mod;
    }

    private final JavaBlock javaBlock;

    /**
     * Creates a modal operator with the given name
     * <strong>Creation must only be done by {@link de.uka.ilkd.key.logic.TermServices}!</strong>
     *
     */
    private Modality(JavaBlock prg, JavaModalityKind kind) {
        super(kind.name(), JavaDLTheory.FORMULA, kind);
        this.javaBlock = prg;
    }

    @Override
    public JavaBlock program() {
        return javaBlock;
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

    protected <T extends org.key_project.logic.Term> void additionalValidTopLevel(T p_term) {
        final Term term = (Term) p_term;
        for (int i = 0, n = arity(); i < n; i++) {
            if (!possibleSub(i, term.sub(i))) {
                throw new TermCreationException(this, term);
            }
        }
    }

    @Override
    public void validTopLevelException(org.key_project.logic.Term term)
            throws TermCreationException {
        if (1 != term.arity()) {
            throw new TermCreationException(this, term);
        }

        if (1 != term.subs().size()) {
            throw new TermCreationException(this, term);
        }

        if (!term.boundVars().isEmpty()) {
            throw new TermCreationException(this, term);
        }

        if (term.sub(0) == null) {
            throw new TermCreationException(this, term);
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

    public static class JavaModalityKind extends Kind {
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
