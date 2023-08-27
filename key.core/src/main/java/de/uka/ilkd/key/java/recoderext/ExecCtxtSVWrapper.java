/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import de.uka.ilkd.key.logic.op.SchemaVariable;

import recoder.java.SourceElement;
import recoder.java.SourceVisitor;

public class ExecCtxtSVWrapper extends ExecutionContext implements KeYRecoderExtension, SVWrapper {

    /**
     *
     */
    private static final long serialVersionUID = 2299515454738715766L;
    SchemaVariable sv = null;


    public ExecCtxtSVWrapper(SchemaVariable sv) {
        this.sv = sv;
    }

    /**
     * sets the schema variable of sort label
     *
     * @param sv the SchemaVariable
     */
    public void setSV(SchemaVariable sv) {
        this.sv = sv;
    }

    /**
     * returns the schema variable of this type sv wrapper
     */
    public SchemaVariable getSV() {
        return sv;
    }

    public SourceElement getFirstElement() {
        return this;
    }

    public ExecutionContext deepClone() {
        return new ExecCtxtSVWrapper(sv);
    }

    // don't think we need it
    public void accept(SourceVisitor v) {
    }


}
