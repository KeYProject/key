/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.settings;


import org.jspecify.annotations.NonNull;

/**
 * This interface is implemented by classes that are used to store settings for different proposes
 * (like active heuristics, which LDTs to use etc.)
 */
public interface Settings {
    /**
     * This method transfers the given configuration information into the local states. The setter
     * methods are used
     * so {@link java.beans.PropertyChangeEvent} should be triggered accordingly to the new state.
     * <p>
     *
     * @param props a non-null references to a configuration object. The state of this object
     *        shall not be changed by the implementations.
     */
    void readSettings(@NonNull Configuration props);

    /**
     * The internal state is stored in the given configuration object. The stored information must
     * be sufficient
     * to restore the local state.
     * <p>
     * The internal state shall not be changed by the implementations.
     *
     * @param props a non-null reference to a configration object, which state is modified
     *        accordingly to the local
     *        internal state.
     */
    void writeSettings(@NonNull Configuration props);


}
