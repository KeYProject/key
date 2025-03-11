/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.abstraction;

/**
 * A program model element representing packages.
 *
 * @author AL
 * @author RN
 */
public class Package implements ClassTypeContainer {

    private final String name;

    /**
     * Creates a new package with the given name, organized by the given program model info.
     *
     * @param name the name of the package.
     */
    public Package(String name) {
        this.name = name;
    }

    /**
     * Returns the name of this package.
     *
     * @return the name of this package.
     */
    public String getName() {
        return name;
    }

    /**
     * Returns the name of this package.
     *
     * @return the full name of this program model element.
     */
    public String getFullName() {
        return getName();
    }

    /**
     * Returns the enclosing package or class type, or method.
     *
     * @return <CODE>null</CODE>.
     */
    public ClassTypeContainer getContainer() {
        return null;
    }

    /**
     * Returns the enclosing package.
     *
     * @return <CODE>null</CODE>.
     */
    public Package getPackage() {
        return this;
    }


}
