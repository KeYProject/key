/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.transformations.pipeline;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.SwitchEntry;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserEnumConstantDeclaration;

import static com.github.javaparser.ast.Modifier.DefaultKeyword.*;

/// This transformation is made to transform any found [EnumDeclaration] into a corresponding
/// [EnumClassDeclaration].
///
/// @author mulbrich, drodt
/// @version 2026-03-03
/// @since 2006-11-20
public class EnumClassAccessExplicit extends JavaTransformerAbstract {
    public EnumClassAccessExplicit(TransformationPipelineServices pipelineServices) {
        super(pipelineServices);
    }

    @Override
    public void apply(CompilationUnit cu) {
        cu.walk(NameExpr.class, it -> {
            if (it.getParentNode().isPresent() && it.getParentNode().get() instanceof SwitchEntry
                    && it.resolve() instanceof JavaParserEnumConstantDeclaration ed) {
                it.replace(
                    new FieldAccessExpr(new NameExpr(ed.getType().toString()), ed.getName()));
            }
        });
    }
}
