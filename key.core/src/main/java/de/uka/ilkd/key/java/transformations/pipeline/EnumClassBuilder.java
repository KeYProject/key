/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.transformations.pipeline;

import java.util.LinkedHashMap;
import java.util.Map;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.stmt.SwitchEntry;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserEnumConstantDeclaration;

public class EnumClassBuilder extends JavaTransformer {
    /// a mapping of enums to the newly created class declarations.
    final Map<EnumDeclaration, EnumClassDeclaration> substitutes = new LinkedHashMap<>();

    public EnumClassBuilder(TransformationPipelineServices pipelineServices) {
        super(pipelineServices);
    }

    @Override
    public void apply(CompilationUnit cu) {
        cu.walk(EnumDeclaration.class, it -> {
            substitutes.put(it, new EnumClassDeclaration(it));
        });
        cu.walk(NameExpr.class, it -> {
            if (it.getParentNode().isPresent() && it.getParentNode().get() instanceof SwitchEntry
                    && it.resolve() instanceof JavaParserEnumConstantDeclaration ed) {
                it.replace(
                    new FieldAccessExpr(new NameExpr(ed.getType().toString()), ed.getName()));
            }
        });
        for (var e : substitutes.entrySet()) {
            e.getKey().replace(e.getValue());
        }
    }
}
