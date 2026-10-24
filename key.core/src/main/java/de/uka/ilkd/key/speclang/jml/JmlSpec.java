/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.speclang.jml;

import java.util.Objects;

import com.github.javaparser.ast.Node;
import org.jspecify.annotations.NonNull;

/**
 * A JML specification construct in its raw, unprocessed form. The specification is given by the
 * wrapped JMLtk AST node (a {@link com.github.javaparser.ast.jml.clauses.JmlContract}, a
 * {@link com.github.javaparser.ast.jml.body.JmlClassExprDeclaration}, ...) which was parsed by
 * JMLtk together with the surrounding Java file.
 * <p>
 * Later stages (see {@code de.uka.ilkd.key.speclang.jml.translation.JmlToTextual}) re-serialize
 * the wrapped node against KeY's own JML grammar and hand the resulting parse trees to the
 * KeY-specific translation.
 *
 * @param node the JMLtk AST node carrying the specification
 */
public record JmlSpec(@NonNull Node node) {
    public JmlSpec {
        Objects.requireNonNull(node, "node must not be null");
    }

    @Override
    public String toString() {
        return node.toString();
    }
}
