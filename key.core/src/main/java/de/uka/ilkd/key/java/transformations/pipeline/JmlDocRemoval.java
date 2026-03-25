/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.transformations.pipeline;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.jml.doc.*;
import org.jspecify.annotations.NonNull;

/**
 *
 * @author Alexander Weigl
 * @version 1 (3/3/26)
 */
public class JmlDocRemoval extends JavaTransformer {
    public JmlDocRemoval(@NonNull TransformationPipelineServices services) {
        super(services);
    }

    @Override
    public void apply(CompilationUnit cu) {
        cu.walk(it -> {
            if (it instanceof Modifier m) {
                if (m.keyword() instanceof JmlDocModifier) {
                    it.remove();
                }
            }

            if (it instanceof JmlDocStmt ||
                    it instanceof JmlDocType ||
                    it instanceof JmlDocDeclaration) {
                it.remove();
            }
        });
    }
}
