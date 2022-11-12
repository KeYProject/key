/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.java.declaration.modifier;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.declaration.Modifier;


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
