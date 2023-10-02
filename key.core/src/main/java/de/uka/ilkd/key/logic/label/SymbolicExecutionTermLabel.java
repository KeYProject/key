/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.label;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;

import org.key_project.logic.Name;

/**
 * Label attached to a symbolic execution thread.
 *
 * @param id The unique ID of this term label in the {@link Sequent}.
 */
public record SymbolicExecutionTermLabel(int id) implements TermLabel {
    /**
     * The unique name of this label.
     */
    public static final Name NAME = new Name("SE");

    /**
     * The name used in {@link Services#getCounter(String)} to keep track of the already used IDs.
     */
    public static final String PROOF_COUNTER_NAME = "SE_LABEL_COUNTER";

    /**
     * Constructor.
     *
     * @param id The unique ID of this term label in the {@link Sequent}.
     */
    public SymbolicExecutionTermLabel {
    }

    /**
     * {@inheritDoc}
     */
    public boolean equals(Object o) {
        return this == o;
    }

    /**
     * {@inheritDoc}
     */
    public String toString() {
        return NAME + "(" + id() + ")";
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object getChild(int i) {
        if (i == 0) {
            return id();
        }
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int getChildCount() {
        return 1;
    }

    /**
     * Returns the unique ID of this label in the {@link Sequent}.
     *
     * @return The unique ID of this label in the {@link Sequent}.
     */
    @Override
    public int id() {
        return id;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Name name() {
        return NAME;
    }
}
