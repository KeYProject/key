/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.ast.reference;

import de.uka.ilkd.key.java.ast.Statement;
import de.uka.ilkd.key.java.ast.expression.Expression;

import org.key_project.util.collection.ImmutableArray;

public interface MethodOrConstructorReference extends MemberReference, ReferencePrefix, Statement {

    /**
     * @return the array wrapper of the argument expressions .
     */
    ImmutableArray<? extends Expression> getArguments();
}
