/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import de.uka.ilkd.key.logic.op.JOperatorSV;

import recoder.java.Identifier;

public class ProgramVariableSVWrapper extends Identifier implements KeYRecoderExtension, SVWrapper {

    /**
     *
     */
    private static final long serialVersionUID = 8398356228769806560L;
    private final JOperatorSV sv;

    public ProgramVariableSVWrapper(JOperatorSV sv) {
        this.sv = sv;
    }

    protected ProgramVariableSVWrapper(ProgramVariableSVWrapper proto) {
        super(proto);
        sv = proto.getSV();
    }

    /**
     * returns the schema variable of this type sv wrapper
     */
    public JOperatorSV getSV() {
        return sv;
    }



}
