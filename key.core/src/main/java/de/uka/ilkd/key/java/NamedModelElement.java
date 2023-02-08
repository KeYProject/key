/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.java;

/**
 * A model element that carries a name.
 */
public interface NamedModelElement extends ModelElement {

    /**
     * Return the name of the model element.
     *
     * @return the name of the model element.
     */
    String getName();

}
