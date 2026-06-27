/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

import java.util.ArrayList;
import java.util.List;

/**
 * Represents a list of declarations in a KeY specification file.
 * Corresponds to the grammar rule: decls
 *
 * @author Cline
 * @version 1.0
 */
@NullMarked
public class DeclList extends BaseAstNode {
    private final List<Declaration> declarations;

    public DeclList(Position position,
                    List<Declaration> declarations) {
        super(position);
        this.declarations = declarations;
        for (Declaration decl : declarations) {
            setChildParent(decl);
        }
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }

    public List<Declaration> getDeclarations() {
        return declarations;
    }

    public void addDeclaration(Declaration decl) {
        declarations.add(decl);
        setChildParent(decl);
    }
}