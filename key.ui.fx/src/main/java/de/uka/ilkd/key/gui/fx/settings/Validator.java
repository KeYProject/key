/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.settings;

/**
 * A validator for input components of a settings panel, counter-part of {@code Validator} of the
 * Swing module {@code key.ui}.
 *
 * @author Alexander Weigl
 */
@FunctionalInterface
public interface Validator<T> {

    /**
     * Validates the given value; the empty implementation accepts everything.
     *
     * @param obj the value to validate
     * @throws Exception if the value is rejected; the message is shown as a tooltip on the
     *         rejected input component
     */
    void validate(T obj) throws Exception;
}
