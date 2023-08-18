/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.model;

/**
 * Provides the settings used to construct the symbolic execution tree.
 *
 * @author Martin Hentschel
 */
public interface ITreeSettings {
    /**
     * Checks if multiple branch conditions are merged or not.
     *
     * @return {@code true} merge branch conditions which means that a branch condition never
     *         contains another branch condition or {@code false} allow that branch conditions
     *         contains branch conditions.
     */
    boolean isMergeBranchConditions();

    /**
     * Checks if unicode characters are used.
     *
     * @return {@code true} use unicode characters, {@code false} do not use unicode characters.
     */
    boolean isUseUnicode();

    /**
     * Checks if pretty printing is used or not.
     *
     * @return {@code true} use pretty printing, {@code false} do not use pretty printing.
     */
    boolean isUsePrettyPrinting();

    /**
     * Checks how variables are computed.
     *
     * @return {@code true} {@link IExecutionVariable} are only computed from updates, {@code false}
     *         {@link IExecutionVariable}s are computed according to the type structure of the
     *         visible memory.
     */
    boolean isVariablesAreOnlyComputedFromUpdates();

    /**
     * Checks if conditions should be simplified or not.
     *
     * @return {@code true} simplify conditions, {@code false} do not simplify conditions.
     */
    boolean isSimplifyConditions();
}
