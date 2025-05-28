/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import de.uka.ilkd.key.logic.op.JOperatorSV;

import recoder.java.SourceVisitor;

public class ExecCtxtSVWrapper extends ExecutionContext implements KeYRecoderExtension, SVWrapper {

    /**
     *
     */
    private static final long serialVersionUID = 2299515454738715766L;
    private final JOperatorSV sv;


    public ExecCtxtSVWrapper(JOperatorSV sv) {
        this.sv = sv;
    }

    /**
     * returns the schema variable of this type sv wrapper
     */
    public JOperatorSV getSV() {
        return sv;
    }

    public ExecutionContext deepClone() {
        return new ExecCtxtSVWrapper(sv);
    }

    // don't think we need it
    public void accept(SourceVisitor v) {
    }


}
