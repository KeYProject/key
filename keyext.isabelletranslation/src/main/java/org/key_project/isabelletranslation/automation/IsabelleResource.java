/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.isabelletranslation.automation;

import de.unruh.isabelle.control.Isabelle;
import de.unruh.isabelle.pure.Theory;

/**
 * An IsabelleResource is a bundling of an Isabelle instance and a {@link Theory} derived from that
 * instance.
 * It can be used to provide solvers with these values for computation.
 */
public interface IsabelleResource {
    /**
     * Checks if the resource has been destroyed. If this is true the resource should not be used
     * anymore.
     *
     * @return true - resource destroyed, false otherwise
     */
    boolean isDestroyed();

    /**
     * Destroys the resource. Usually by destroying the Isabelle instance.
     */
    void destroy();

    /**
     * Interrupts the Isabelle instance.
     */
    void interrupt();

    /**
     * Returns the instance matching the {@link Theory} returned by
     * {@link IsabelleResource#theory()}
     *
     * @return {@link Isabelle} usable with {@link IsabelleResource#theory()}
     */
    Isabelle instance();

    /**
     * Returns the {@link Theory} matching the {@link Isabelle} returned by
     * {@link IsabelleResource#instance()}
     *
     * @return {@link Theory} usable with {@link IsabelleResource#instance()}
     */
    Theory theory();
}
