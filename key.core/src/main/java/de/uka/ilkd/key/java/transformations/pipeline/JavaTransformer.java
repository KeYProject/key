/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.transformations.pipeline;


import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.TypeDeclaration;
import org.jspecify.annotations.NullMarked;

/**
 * A transformation of Java ASTs in an early loading stage.
 * <p>
 * A {@link JavaTransformer} defines a transformation on mutable {@link Node}.
 * As an entry an transformer receives the compilation unit. Traversal of it is left to the
 * implementation of the transformer. The code should be transformed in-place. Creation of new
 * {@link CompilationUnit}
 * is not possible, but the creation of new {@link TypeDeclaration}
 * <p>
 * Implementation should be stateless as instances are reused accross {@link CompilationUnit}s but
 * not across
 * loading requests.
 *
 * @author weigl
 */
@NullMarked
public interface JavaTransformer {
    /// Modifying the given `td` without constraints.
    default void apply(TypeDeclaration<?> td) {
    }

    /// Transform the given {@link CompilationUnit} in place. The default implementation
    /// iterates over all {@link TypeDeclaration}, and calls {@link #apply(TypeDeclaration)}.
    default void apply(CompilationUnit cu) {
        for (TypeDeclaration<?> type : cu.getTypes()) {
            apply(type);
            for (var m : type.getMembers()) {
                if (m instanceof TypeDeclaration<?> ty) {
                    apply(ty);
                }
            }
        }
    }
}
