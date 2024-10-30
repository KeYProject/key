/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast;

import org.key_project.logic.Namespace;
import org.key_project.rusty.logic.op.ProgramVariable;

import org.jspecify.annotations.NonNull;

/**
 * this class stores context information used to parse in program parts in which
 * non-declared variables are used
 */
public class Context {
    public static final String TMP_FN_NAME = "__RUSTY_KEY_CTX_FN_NAME__";
    private final Namespace<@NonNull ProgramVariable> varNS;

    public Context(Namespace<@NonNull ProgramVariable> varNS) {
        this.varNS = varNS;
    }

    public String buildFunction(String block, boolean withAttrs) {
        var sb = new StringBuilder();
        sb.append(
            "#[allow(non_snake_case, unused_mut, dead_code, unused_assignments, unused_variables)]\n");
        sb.append("fn ").append(TMP_FN_NAME).append("(");
        for (ProgramVariable pv : varNS.allElements()) {
            sb.append(pv.name()).append(": ");
            sb.append(getType(pv));
            sb.append(", ");
        }
        sb.append(") {");
        sb.append(block);
        sb.append(";\n");
        sb.append("}");
        return sb.toString();
    }

    public String buildFunction(String block) {
        return buildFunction(block, false);
    }

    private String getType(ProgramVariable pv) {
        return "u32";
    }
}
