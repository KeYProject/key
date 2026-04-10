/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.model.impl;

import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;
import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;

/**
 * The default implementation of {@link ITreeSettings}.
 *
 * @param mergeBranchConditions {@code true} merge branch conditions which means that a branch
 *        condition never contains
 *        another branch condition or {@code false} allow that branch conditions contains branch
 *        conditions.
 * @param useUnicode {@code true} use unicode characters, {@code false} do not use unicode
 *        characters.
 * @param usePrettyPrinting {@code true} use pretty printing, {@code false} do not use pretty
 *        printing.
 * @param variablesAreOnlyComputedFromUpdates {@code true} {@link IExecutionVariable} are only
 *        computed from updates, {@code false}
 *        {@link IExecutionVariable}s are computed according to the type structure of the visible
 *        memory.
 * @param simplifyConditions {@code true} simplify conditions, {@code false} do not simplify
 *        conditions.
 * @author Martin Hentschel
 */
public record TreeSettings(boolean mergeBranchConditions, boolean useUnicode,
        boolean usePrettyPrinting, boolean variablesAreOnlyComputedFromUpdates,
        boolean simplifyConditions) implements ITreeSettings {
    /**
     * Constructor.
     *
     * @param mergeBranchConditions {@code true} merge branch conditions which means that a branch
     *        condition never contains another branch condition or {@code false} allow that branch
     *        conditions contains branch conditions.
     * @param useUnicode {@code true} use unicode characters, {@code false} do not use unicode
     *        characters.
     * @param usePrettyPrinting {@code true} use pretty printing, {@code false} do not use pretty
     *        printing.
     * @param variablesAreOnlyComputedFromUpdates {@code true} {@link IExecutionVariable} are only
     *        computed from updates, {@code false} {@link IExecutionVariable}s are computed
     *        according to the type structure of the visible memory.
     * @param simplifyConditions {@code true} simplify conditions, {@code false} do not simplify
     *        conditions.
     */
    public TreeSettings {
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean mergeBranchConditions() { return mergeBranchConditions; }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean useUnicode() { return useUnicode; }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean usePrettyPrinting() { return usePrettyPrinting; }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean variablesAreOnlyComputedFromUpdates() {
        return variablesAreOnlyComputedFromUpdates;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean simplifyConditions() { return simplifyConditions; }
}
