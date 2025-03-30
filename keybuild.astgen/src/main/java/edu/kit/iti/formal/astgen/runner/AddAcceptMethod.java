/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package edu.kit.iti.formal.astgen.runner;

import javax.lang.model.element.Modifier;

import com.palantir.javapoet.*;
import edu.kit.iti.formal.astgen.model.Node;

/**
 * @author Alexander Weigl
 * @version 1 (10.09.17)
 */
public class AddAcceptMethod extends AbstractNodeGenerator {
    static TypeVariableName typeR = TypeVariableName.get("R");

    public static MethodSpec generateAccept(int args) {
        String name = args == 0 ? "accept" : "accept" + args;
        ParameterizedTypeName visitor = ParameterizedTypeName.get(
            ClassName.get("", "Visitor"), typeR);

        var m = MethodSpec.methodBuilder(name)
                .addModifiers(Modifier.PUBLIC)
                .addTypeVariable(typeR)
                .addParameter(visitor, "args")
                .addAnnotation(Override.class);

        String arguments = "";
        for (int i = 0; i < args; i++) {
            var t = TypeVariableName.get("T" + i);
            m.addTypeVariable(t);
            m.addParameter(t, "arg" + i);
            arguments += ", arg" + i;
        }
        return m.addCode("return visitor.accept(this" + arguments + ");")
                .build();
    }

    @Override
    public TypeSpec.Builder modify(Node node, TypeSpec.Builder unit) {
        unit.addMethod(generateAccept(0));
        unit.addMethod(generateAccept(1));
        return unit;
    }
}
