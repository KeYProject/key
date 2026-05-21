/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.transformations.pipeline;

import java.util.LinkedHashMap;
import java.util.Map;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.AnnotationDeclaration;

/**
 * This class converts {@link AnnotationDeclaration}s to 
 * {@link AnnotationInterfaceDeclaration}s
 *
 * @author PiIsRational
 */
public class AnnotationInterfaceBuilder extends JavaTransformerAbstract {
    /** 
     * a mapping of {@link AnnotationDeclarations} to 
     * {@link AnnotationInterfaceDeclarations} */
    final Map<AnnotationDeclaration, AnnotationInterfaceDeclarationNode> substitutes = new LinkedHashMap<>();

    public AnnotationInterfaceBuilder(
            TransformationPipelineServices pipelineServices) {
        super(pipelineServices);
    }

    @Override
    public void apply(CompilationUnit cu) {
        cu.walk(AnnotationDeclaration.class, it -> {
            substitutes.put(it, new AnnotationInterfaceDeclarationNode(it));
        });
        for (var e : substitutes.entrySet()) {
            e.getKey().replace(e.getValue());
        }
    }
}
