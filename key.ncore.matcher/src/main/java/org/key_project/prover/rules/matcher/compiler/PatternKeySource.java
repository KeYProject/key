/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.matcher.compiler;

import org.key_project.logic.op.sv.SchemaVariable;

/**
 * For a taclet's {@code \assumes} formula, where a lookup key for it can be taken from.
 *
 * <p>
 * The rule-application queue sets aside ("parks") a rule whose {@code \assumes} formula is not
 * yet in the sequent, and wakes it when a matching formula appears. To find the waiting rules
 * quickly it files each one under a key and looks newly added formulas up by the same key, so
 * the key must be one that every formula the {@code \assumes} could match produces. An
 * {@code \assumes} formula is a pattern: a fixed term shape in which a schema variable stands
 * for an arbitrary term. This type says, for one such pattern, what its key can be built from.
 * It is computed by {@link MatchPlanBuilder#keySourceFor} from the same per-operator dispatch
 * the matcher runs on, so it always agrees with what the matcher accepts.
 *
 * <p>
 * Three cases:
 * <ul>
 * <li>{@link ByHead}: the pattern's top operator is a concrete operator. Every term the pattern
 * matches then has a top operator of one operator family, named by {@code headDescriptor} (two
 * operators of the same family compare equal, see {@link MatchHead#topOperatorDescriptor()});
 * {@code firstArg} optionally adds the family of the first subterm.</li>
 * <li>{@link ByWholeSchemaVariable}: the pattern is a single schema variable and matches any
 * term, so no key is fixed in advance; a key can only be read off the term the variable is
 * instantiated with.</li>
 * <li>{@link Unkeyable}: no key can be built, so a client files nothing for this pattern and
 * keeps considering the candidate the ordinary way, which never sets a candidate aside wrongly.
 * This is also the result for any construct the builder does not recognize, so it is the safe
 * default. It arises for example when the top is a schematic modality kind, which stands for
 * several concrete kinds at once.</li>
 * </ul>
 */
public sealed interface PatternKeySource {

    /**
     * The pattern's top operator is concrete: every term it matches has a top operator of the
     * family {@code headDescriptor}, and {@code firstArg} gives the family of the first subterm.
     *
     * @param headDescriptor the operator family of the pattern's top, never {@code null}
     * @param firstArg the family of the pattern's first subterm ({@link FirstArg.None} for a
     *        pattern without subterms)
     */
    record ByHead(Object headDescriptor, FirstArg firstArg) implements PatternKeySource {
    }

    /**
     * The pattern is a single schema variable and accepts any term; a key can only come from the
     * variable's instantiation.
     *
     * @param sv the pattern's schema variable
     */
    record ByWholeSchemaVariable(SchemaVariable sv) implements PatternKeySource {
    }

    /** No key can be derived from this pattern. */
    record Unkeyable() implements PatternKeySource {
        /** the single instance; the record carries no data */
        public static final Unkeyable INSTANCE = new Unkeyable();
    }

    /**
     * The family of a pattern's first subterm, used to tell apart patterns that share a top
     * operator but differ one level down.
     */
    sealed interface FirstArg {

        /** The pattern has no subterms, or no family can be built for its first subterm. */
        record None() implements FirstArg {
            /** the single instance; the record carries no data */
            public static final None INSTANCE = new None();
        }

        /**
         * The first subterm's top operator is concrete and belongs to the family
         * {@code descriptor}.
         *
         * @param descriptor the operator family of the first subterm's top, never {@code null}
         */
        record ByArgHead(Object descriptor) implements FirstArg {
        }

        /**
         * The first subterm is a schema variable; a key can only come from its instantiation.
         *
         * @param sv the first subterm's schema variable
         */
        record ByArgSchemaVariable(SchemaVariable sv) implements FirstArg {
        }
    }
}
