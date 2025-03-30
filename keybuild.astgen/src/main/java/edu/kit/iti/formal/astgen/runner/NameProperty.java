/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package edu.kit.iti.formal.astgen.runner;

import javax.lang.model.element.Modifier;

import com.palantir.javapoet.MethodSpec;
import com.palantir.javapoet.TypeSpec;
import edu.kit.iti.formal.astgen.model.Node;

/**
 * @author Alexander Weigl
 * @version 1 (10.09.17)
 */
public class NameProperty extends AbstractNodeGenerator {
    @Override
    public TypeSpec.Builder modify(Node node, TypeSpec.Builder unit) {
        unit.addMethod(MethodSpec.methodBuilder("getName")
                .returns(String.class)
                .addModifiers(Modifier.PUBLIC)
                .addAnnotation(Override.class)
                .addCode("return $L;", node.name())
                .build());
        return unit;
    }
}
