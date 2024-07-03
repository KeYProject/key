/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package de.uka.ilkd.key.testgen.oracle;

import java.util.List;

public class OracleMethodCall implements OracleTerm {

    private OracleMethod method;
    private List<? extends OracleTerm> args;
    private OracleTerm caller;

    public OracleMethodCall(OracleMethod method, List<? extends OracleTerm> args) {
        super();
        this.method = method;
        this.args = args;
        caller = null;
    }

    public OracleMethodCall(OracleMethod method, List<? extends OracleTerm> args,
            OracleTerm caller) {
        super();
        this.method = method;
        this.args = args;
        this.caller = caller;
    }

    public String toString() {
        String methodName = method.getMethodName();
        String aString = "";
        for (OracleTerm arg : args) {
            aString += " " + arg.toString() + ",";
        }
        if (!args.isEmpty()) {
            aString = aString.substring(0, aString.length() - 1);
        }
        if (caller != null) {
            return caller + "." + methodName + "(" + aString + ")";
        } else {
            return methodName + "(" + aString + ")";
        }
    }

}
