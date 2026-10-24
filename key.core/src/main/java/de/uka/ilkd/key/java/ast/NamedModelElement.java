/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.ast;

import org.jspecify.annotations.NullMarked;

/**
 * A model element that carries a name.
 */
@NullMarked
public interface NamedModelElement extends ModelElement {

    /**
     * Return the name of the model element.
     *
     * @return the name of the model element.
     */
    String getName();

}
