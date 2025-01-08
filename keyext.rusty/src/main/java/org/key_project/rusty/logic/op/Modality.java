/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic.op;

import java.lang.ref.WeakReference;
import java.util.HashMap;
import java.util.Map;
import java.util.WeakHashMap;

import org.key_project.logic.Name;
import org.key_project.logic.TermCreationException;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.logic.RustyBlock;
import org.key_project.rusty.logic.RustyDLTheory;
import org.key_project.util.collection.Pair;

import org.jspecify.annotations.NonNull;

/**
 * This class is used to represent a dynamic logic modality like diamond and box (but also
 * extensions of DL like preserves and throughout are possible in the future).
 */
public class Modality extends org.key_project.logic.op.Modality {
    /**
     * keeps track of created modalities
     */
    private static final Map<RustyProgramElement, WeakHashMap<RustyModalityKind, WeakReference<Modality>>> modalities =
        new WeakHashMap<>();

    /**
     * Retrieves the modality of the given kind and program.
     *
     * @param kind the kind of the modality such as diamond or box
     * @param rb the program of this modality
     * @return the modality of the given kind and program.
     */
    public static synchronized Modality getModality(RustyModalityKind kind, RustyBlock rb) {
        var kind2mod = modalities.get(rb.program());
        final Modality mod;
        WeakReference<Modality> modRef;
        if (kind2mod == null) {
            kind2mod = new WeakHashMap<>();
            mod = new Modality(rb, kind);
            modRef = new WeakReference<>(mod);
            kind2mod.put(kind, modRef);
            modalities.put(rb.program(), kind2mod);
        } else {
            modRef = kind2mod.get(kind);
            if (modRef == null || modRef.get() == null) {
                mod = new Modality(rb, kind);
                modRef = new WeakReference<>(mod);
                kind2mod.put(kind, modRef);
                modalities.put(rb.program(), kind2mod);
            } else {
                mod = modRef.get();
            }
        }
        return mod;
    }

    private final RustyBlock block;

    /**
     * Creates a modal operator with the given name
     * <strong>Creation must only be done by ???!</strong>
     *
     */
    private Modality(RustyBlock prg, RustyModalityKind kind) {
        super(kind.name(), RustyDLTheory.FORMULA, kind);
        this.block = prg;
    }

    @Override
    public @NonNull RustyBlock program() {
        return block;
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
    }

    public static class RustyModalityKind extends Kind {
        private static final Map<String, RustyModalityKind> kinds = new HashMap<>();
        /**
         * The diamond operator of dynamic logic. A formula <alpha;>Phi can be read as after
         * processing
         * the program alpha there exists a state such that Phi holds.
         */
        public static final RustyModalityKind DIA = new RustyModalityKind(new Name("diamond"));
        /**
         * The box operator of dynamic logic. A formula [alpha;]Phi can be read as 'In all states
         * reachable processing the program alpha the formula Phi holds'.
         */
        public static final RustyModalityKind BOX = new RustyModalityKind(new Name("box"));

        public RustyModalityKind(Name name) {
            super(name);
            kinds.put(name.toString(), this);
        }

        public static RustyModalityKind getKind(String name) {
            return kinds.get(name);
        }

        /**
         * Whether this modality is termination sensitive, i.e., it is a "diamond-kind" modality.
         */
        public boolean terminationSensitive() {
            return (this == DIA);
        }
    }
}
