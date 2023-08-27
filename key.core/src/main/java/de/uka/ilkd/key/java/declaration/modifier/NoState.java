/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.declaration.modifier;

import de.uka.ilkd.key.java.declaration.Modifier;

import org.key_project.util.ExtList;


/**
 * The JML modifier "no_state".
 */
public class NoState extends Modifier {

    public NoState() {}


    public NoState(ExtList children) {
        super(children);
    }


    protected String getSymbol() {
        return "no_state";
    }
}
