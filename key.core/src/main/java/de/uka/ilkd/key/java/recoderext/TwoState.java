/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import recoder.java.SourceVisitor;
import recoder.java.declaration.Modifier;


public class TwoState extends Modifier {

    private static final long serialVersionUID = 1408979308814683681L;

    public TwoState() {
    }

    protected TwoState(TwoState proto) {
        super(proto);
    }

    public TwoState deepClone() {
        return new TwoState(this);
    }

    public void accept(SourceVisitor v) {
    }

}
