/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.model.impl;

import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;
import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;

/**
 * The default implementation of {@link ITreeSettings}.
 *
 * @author Martin Hentschel
 */
public class TreeSettings implements ITreeSettings {
    /**
     * {@code true} merge branch conditions which means that a branch condition never contains
     * another branch condition or {@code false} allow that branch conditions contains branch
     * conditions.
     */
    private final boolean mergeBranchConditions;

    /**
     * {@code true} use unicode characters, {@code false} do not use unicode characters.
     */
    private final boolean useUnicode;

    /**
     * {@code true} use pretty printing, {@code false} do not use pretty printing.
     */
    private final boolean usePrettyPrinting;

    /**
     * {@code true} {@link IExecutionVariable} are only computed from updates, {@code false}
     * {@link IExecutionVariable}s are computed according to the type structure of the visible
     * memory.
     */
    private final boolean variablesAreOnlyComputedFromUpdates;

    /**
     * {@code true} simplify conditions, {@code false} do not simplify conditions.
     */
    private final boolean simplifyConditions;

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
    public TreeSettings(boolean mergeBranchConditions, boolean useUnicode,
            boolean usePrettyPrinting, boolean variablesAreOnlyComputedFromUpdates,
            boolean simplifyConditions) {
        this.mergeBranchConditions = mergeBranchConditions;
        this.useUnicode = useUnicode;
        this.usePrettyPrinting = usePrettyPrinting;
        this.variablesAreOnlyComputedFromUpdates = variablesAreOnlyComputedFromUpdates;
        this.simplifyConditions = simplifyConditions;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isMergeBranchConditions() {
        return mergeBranchConditions;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isUseUnicode() {
        return useUnicode;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isUsePrettyPrinting() {
        return usePrettyPrinting;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isVariablesAreOnlyComputedFromUpdates() {
        return variablesAreOnlyComputedFromUpdates;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isSimplifyConditions() {
        return simplifyConditions;
    }
}
