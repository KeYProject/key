/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Represents a datatype constructor.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * datatype_constructor: name=simple_ident arg_sorts;
 * }</pre>
 */
@NullMarked
public class DatatypeConstructor extends BaseAstNode {
    private final SimpleIdentDots name;
    private final ArgSorts argSorts;

    public DatatypeConstructor(Position position, SimpleIdentDots name, ArgSorts argSorts) {
        super(position);
        this.name = name;
        this.argSorts = argSorts;
        setChildParent(name);
        setChildParent(argSorts);
    }

    public SimpleIdentDots getName() {
        return name;
    }

    public ArgSorts getArgSorts() {
        return argSorts;
    }
}