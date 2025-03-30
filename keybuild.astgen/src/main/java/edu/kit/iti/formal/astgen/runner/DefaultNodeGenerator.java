/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package edu.kit.iti.formal.astgen.runner;

import javax.annotation.processing.Generated;
import javax.lang.model.element.Modifier;

import com.palantir.javapoet.ClassName;
import com.palantir.javapoet.TypeSpec;
import edu.kit.iti.formal.astgen.model.Node;

/**
 * @author Alexander Weigl
 * @version 1 (10.09.17)
 */
public class DefaultNodeGenerator extends AbstractNodeGenerator {
    @Override
    public TypeSpec.Builder modify(Node node, TypeSpec.Builder unit) {
        unit.addModifiers(Modifier.PUBLIC);
        if (node.isAbstract())
            unit.addModifiers(Modifier.ABSTRACT);
        if (node.isFinal())
            unit.addModifiers(Modifier.FINAL);

        if (node.extendz().node() != null)
            unit.addSuperinterface(ClassName.bestGuess(node.extendz().node().name()));

        for (Node inter : node.implementz()) {
            unit.addSuperinterface(ClassName.bestGuess(inter.name()));
        }

        unit.addAnnotation(Generated.class);

        if (node.comment() != null) {
            unit.addJavadoc(node.comment());
        }
        return unit;
    }
}
