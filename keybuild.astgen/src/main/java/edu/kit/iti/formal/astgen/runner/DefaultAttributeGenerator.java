/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package edu.kit.iti.formal.astgen.runner;

import javax.lang.model.element.Modifier;

import com.palantir.javapoet.MethodSpec;
import com.palantir.javapoet.TypeSpec;
import edu.kit.iti.formal.astgen.model.Attr;
import edu.kit.iti.formal.astgen.model.Node;
import org.jspecify.annotations.Nullable;

/**
 * @author Alexander Weigl
 * @version 1 (10.09.17)
 */
public class DefaultAttributeGenerator extends AbstractNodeGenerator {
    @Override
    public TypeSpec.Builder modify(Node node, TypeSpec.Builder unit) {
        for (Attr attr : node.attributes()) {
            var field = unit.addField(attr.type(), attr.name(), Modifier.PROTECTED, Modifier.FINAL);

            if (attr.nullable()) {
                field.addAnnotation(Nullable.class);
            }

            if (attr.comment() != null) {
                field.addJavadoc(attr.comment());
            }

            unit.addMethod(MethodSpec.methodBuilder(attr.name())
                    .returns(attr.type())
                    .addModifiers(Modifier.PUBLIC, Modifier.FINAL)
                    .addJavadoc(attr.comment() != null ? attr.comment() : "")
                    .addCode("return $N;", attr.name())
                    .build());
        }

        return unit;
    }
}
