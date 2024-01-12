/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.abstraction;

/**
 * A program model element that may contain class types.
 */
public interface ClassTypeContainer extends ProgramModelElement {

    /**
     * Returns the class types locally defined within this container. Returns inner types when this
     * container is a class type.
     *
     * @return an array of contained class types.
     */
    // ClassType[] getTypes();

    /**
     * Returns the package this element is defined in. Packages have no recursive scope and report
     * themselves.
     *
     * @return the package of this element.
     */
    // Package getPackage();

    /**
     * Returns the enclosing package or class type, or method. A package will report <tt>null</tt>,
     * a methods its enclosing class.
     *
     * @return the container of this element.
     */
    // ClassTypeContainer getContainer();

}
