/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.logic;

/**
 * This interface has to be implemented by all logic signature elements, which are identified by
 * their name.
 */
public interface Named {

    /**
     * returns the name of this element
     *
     * @return the name of the element
     */
    Name name();

}
