/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.transformations.pipeline;

import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.expr.StringLiteralExpr;
import com.github.javaparser.ast.expr.TextBlockLiteralExpr;

/**
 *
 * @author Alexander Weigl
 * @version 1 (3/31/26)
 */
public class TextblockTransformer implements JavaTransformer {
    @Override
    public void apply(TypeDeclaration<?> td) {
        for (var textblock : td.findAll(TextBlockLiteralExpr.class)) {
            var s = textblock.getValue().stripIndent().translateEscapes()
                    .replace("\\\n", "")
                    .replace("\"", "\\\"");
            var literal = new StringLiteralExpr(s);
            textblock.replace(literal);
        }
    }
}
