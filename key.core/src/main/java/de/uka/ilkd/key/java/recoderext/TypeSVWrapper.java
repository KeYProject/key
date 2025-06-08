/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import de.uka.ilkd.key.logic.op.JOperatorSV;

import recoder.java.SourceElement;
import recoder.java.reference.TypeReference;

public class TypeSVWrapper extends TypeReference implements KeYRecoderExtension, SVWrapper {

    /**
     *
     */
    private static final long serialVersionUID = 2694567717981292433L;
    private final JOperatorSV sv;

    public TypeSVWrapper(JOperatorSV sv) {
        this.sv = sv;
    }

    protected TypeSVWrapper(TypeSVWrapper proto) {
        super(proto);
        sv = proto.getSV();
    }

    /**
     * returns the schema variable of this type sv wrapper
     */
    public JOperatorSV getSV() {
        return sv;
    }

    public SourceElement getFirstElement() {
        return this;
    }


}
