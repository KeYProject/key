/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testgen.oracle;

import java.util.List;

import de.uka.ilkd.key.logic.sort.Sort;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.ParameterSpec;
import com.squareup.javapoet.TypeName;

import static de.uka.ilkd.key.testgen.template.Constants.TAB;

public class OracleMethod {

    private final String methodName;

    private final List<OracleVariable> args;

    private final String body;

    private Sort returnType;

    public OracleMethod(String methodName, List<OracleVariable> args, String body) {
        super();
        this.methodName = methodName;
        this.args = args;
        this.body = body;
    }

    public OracleMethod(String methodName, List<OracleVariable> args, String body, Sort sort) {
        super();
        this.methodName = methodName;
        this.args = args;
        this.body = body;
        this.returnType = sort;
    }

    public String getMethodName() {
        return methodName;
    }

    public List<OracleVariable> getArgs() {
        return args;
    }

    public String getBody() {
        return body;
    }

    public MethodSpec build() {
        TypeName retType = TypeName.BOOLEAN;
        if (returnType != null) {
            retType = ClassName.get("", returnType.name().toString());
        }

        Iterable<ParameterSpec> params = args.stream().map(
            it -> ParameterSpec.builder(ClassName.get("", it.sort().name().toString()),
                it.name().toString()).build()).toList();

        var m = MethodSpec.methodBuilder(methodName)
                .returns(retType)
                .addParameters(params)
                .addStatement(body);
        return m.build();
    }

    @Override
    public String toString() {
        String tab = TAB;
        StringBuilder argString = new StringBuilder();

        for (OracleVariable var : args) {
            argString.append(var.sort().name()).append(" ").append(var.name()).append(",");
        }
        if (!args.isEmpty()) {
            argString = new StringBuilder(argString.substring(0, argString.length() - 1));
        }

        String retType = "boolean";
        if (returnType != null) {
            retType = returnType.name().toString();
        }
        return tab + "public " + retType + " " + methodName + "(" + argString + "){\n" + tab + tab
            + body + "\n" + tab + "}";

    }
}
