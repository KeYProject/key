/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.declaration.modifier;

import java.util.List;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.declaration.Modifier;


/**
 * The JML modifier "model".
 */
public class Model extends Modifier {

    public Model() {}


    public Model(PositionInfo pi, List<Comment> c) {
        super(pi, c);
    }


    protected String getSymbol() {
        return "model";
    }
}