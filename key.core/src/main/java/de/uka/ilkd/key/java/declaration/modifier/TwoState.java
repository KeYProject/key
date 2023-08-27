/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.declaration.modifier;

import de.uka.ilkd.key.java.declaration.Modifier;

import org.key_project.util.ExtList;


/**
 * The JML modifier "two_state".
 */
public class TwoState extends Modifier {

    public TwoState() {}


    public TwoState(ExtList children) {
        super(children);
    }


    protected String getSymbol() {
        return "two_state";
    }
}
