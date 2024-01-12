/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import recoder.java.SourceVisitor;
import recoder.java.declaration.Modifier;


public class Ghost extends Modifier {

    /**
     *
     */
    private static final long serialVersionUID = -4883937081008486072L;


    public Ghost() {
    }


    protected Ghost(Ghost proto) {
        super(proto);
    }


    public Ghost deepClone() {
        return new Ghost(this);
    }


    public void accept(SourceVisitor v) {
    }
}
