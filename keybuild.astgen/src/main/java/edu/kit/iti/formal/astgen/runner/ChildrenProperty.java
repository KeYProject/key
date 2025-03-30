/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package edu.kit.iti.formal.astgen.runner;

import java.util.Collection;
import javax.lang.model.element.Modifier;

import com.palantir.javapoet.CodeBlock;
import com.palantir.javapoet.MethodSpec;
import com.palantir.javapoet.ParameterizedTypeName;
import com.palantir.javapoet.TypeSpec;
import edu.kit.iti.formal.astgen.model.Attr;
import edu.kit.iti.formal.astgen.model.Node;

/**
 * @author Alexander Weigl
 * @version 1 (10.09.17)
 */
public class ChildrenProperty extends AbstractNodeGenerator {
    @Override
    public TypeSpec.Builder modify(Node node, TypeSpec.Builder unit) {
        var code = CodeBlock.builder();
        code.addStatement("List<Object> rt = new ArrayList<>($L);", node.attributes().size());
        for (Attr attribute : node.attributes()) {
            code.addStatement("rt.add($T)", attribute.name());
        }
        code.addStatement("return rt;");

        var m = MethodSpec.methodBuilder("getChildren")
                .returns(ParameterizedTypeName.get(Collection.class, Object.class))
                .addAnnotation(Override.class)
                .addModifiers(Modifier.PUBLIC)
                .addCode(code.build());
        unit.addMethod(m.build());
        return unit;
    }
}
