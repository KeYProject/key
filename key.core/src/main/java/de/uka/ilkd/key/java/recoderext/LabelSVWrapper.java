/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import de.uka.ilkd.key.logic.op.OperatorSV;

import recoder.java.Identifier;

public class LabelSVWrapper extends Identifier implements KeYRecoderExtension, SVWrapper {

    /**
     *
     */
    private static final long serialVersionUID = 5338442155201858492L;
    private final OperatorSV sv;

    public LabelSVWrapper(OperatorSV sv) {
        this.sv = sv;
    }

    protected LabelSVWrapper(LabelSVWrapper proto) {
        super(proto);
        sv = proto.getSV();
        id = proto.id;
    }

    /**
     * returns the schema variable of this label sv wrapper
     */
    public OperatorSV getSV() {
        return sv;
    }


}
