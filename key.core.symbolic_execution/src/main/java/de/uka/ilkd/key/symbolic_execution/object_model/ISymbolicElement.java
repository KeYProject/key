/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.object_model;

/**
 * Defines the basic methods and properties each element in an symbolic object model has to have.
 *
 * @author Martin Hentschel
 */
public interface ISymbolicElement {
    /**
     * Returns the {@link IModelSettings} to use.
     *
     * @return The {@link IModelSettings} to use.
     */
    IModelSettings getSettings();
}
