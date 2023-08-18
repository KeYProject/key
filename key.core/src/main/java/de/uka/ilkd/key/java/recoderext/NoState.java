/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import recoder.java.SourceVisitor;
import recoder.java.declaration.Modifier;


public class NoState extends Modifier {

    private static final long serialVersionUID = 2717863742463891263L;

    public NoState() {
    }


    protected NoState(NoState proto) {
        super(proto);
    }

    public NoState deepClone() {
        return new NoState(this);
    }

    public void accept(SourceVisitor v) {
    }

}
