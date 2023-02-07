/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.symbolic_execution.object_model;

/**
 * Provides the settings used to construct a symbolic object model.
 *
 * @author Martin Hentschel
 */
public interface IModelSettings {
    /**
     * Checks if unicode characters are used.
     *
     * @return {@code true} use unicode characters, {@code false} do not use unicode characters.
     */
    public boolean isUseUnicode();

    /**
     * Checks if pretty printing is used or not.
     *
     * @return {@code true} use pretty printing, {@code false} do not use pretty printing.
     */
    public boolean isUsePrettyPrinting();

    /**
     * Checks if conditions should be simplified or not.
     *
     * @return {@code true} simplify conditions, {@code false} do not simplify conditions.
     */
    public boolean isSimplifyConditions();
}
