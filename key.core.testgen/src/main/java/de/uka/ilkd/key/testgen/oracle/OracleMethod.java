/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testgen.oracle;

import java.util.List;

import de.uka.ilkd.key.testgen.TestCaseGenerator;

import org.key_project.logic.sort.Sort;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.ParameterSpec;
import com.squareup.javapoet.TypeName;
import org.jspecify.annotations.Nullable;

import static de.uka.ilkd.key.testgen.Constants.TAB;

public class OracleMethod {

    private final String methodName;

    private final List<OracleVariable> args;

    private final String body;

    private @Nullable Sort returnType;

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
            it -> ParameterSpec.builder(TestCaseGenerator.getTypeName(it.sort()),
                it.name()).build()).toList();

        var m = MethodSpec.methodBuilder(methodName)
                .returns(retType)
                .addParameters(params);
        addBody(m);
        return m.build();
    }

    protected void addBody(MethodSpec.Builder m) {
        m.addStatement(body);
    }

    @Override
    public String toString() {
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
        return "%spublic %s %s(%s){\n%s%s%s\n%s}".formatted(TAB, retType, methodName, argString,
            TAB, TAB, body, TAB);

    }
}
