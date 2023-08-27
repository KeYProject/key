/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import de.uka.ilkd.key.logic.op.SchemaVariable;

import recoder.java.Identifier;

public class ProgramVariableSVWrapper extends Identifier implements KeYRecoderExtension, SVWrapper {

    /**
     *
     */
    private static final long serialVersionUID = 8398356228769806560L;
    SchemaVariable sv = null;

    public ProgramVariableSVWrapper(SchemaVariable sv) {
        this.sv = sv;
    }

    protected ProgramVariableSVWrapper(ProgramVariableSVWrapper proto) {
        super(proto);
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



}
