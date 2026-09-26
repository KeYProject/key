/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.ast;

public class ParentIsInterfaceDeclaration {

    private final boolean value;

    public ParentIsInterfaceDeclaration(boolean val) {
        this.value = val;
    }

    public boolean getValue() {
        return value;
    }

}
