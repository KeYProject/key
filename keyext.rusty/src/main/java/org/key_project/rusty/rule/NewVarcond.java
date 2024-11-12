/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule;

import org.key_project.rusty.ast.abstraction.KeYRustyType;
import org.key_project.rusty.logic.op.sv.SchemaVariable;

public class NewVarcond {
    private final SchemaVariable sv;
    private final SchemaVariable peerSV;
    private final KeYRustyType type;

    public NewVarcond(SchemaVariable sv, SchemaVariable peerSV) {
        assert sv != null;
        assert peerSV != null;
        this.sv = sv;
        this.peerSV = peerSV;
        type = null;
    }

    public NewVarcond(SchemaVariable sv, KeYRustyType type) {
        assert sv != null;
        assert type != null;
        this.sv = sv;
        this.peerSV = null;
        this.type = type;
    }

    public SchemaVariable getSchemaVariable() {
        return sv;
    }

    public SchemaVariable getPeerSchemaVariable() {
        return peerSV;
    }

    public KeYRustyType getType() {
        return type;
    }

    public Object getTypeDefiningObject() {
        return type != null ? type : peerSV;
    }
}
