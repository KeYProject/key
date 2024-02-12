/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testgen.oracle;

import java.util.List;
import java.util.stream.Collectors;

import org.jspecify.annotations.Nullable;

public record OracleMethodCall(OracleMethod method, List<? extends OracleTerm> args,
                               @Nullable OracleTerm caller)
        implements OracleTerm {
    public OracleMethodCall(OracleMethod method, List<? extends OracleTerm> args) {
        this(method, args, null);
    }

    public String toString() {
        String methodName = method.getMethodName();
        String aString = args.stream().map(Object::toString).collect(Collectors.joining(", "));
        if (caller != null) {
            return caller + "." + methodName + "(" + aString + ")";
        } else {
            return methodName + "(" + aString + ")";
        }
    }
}
