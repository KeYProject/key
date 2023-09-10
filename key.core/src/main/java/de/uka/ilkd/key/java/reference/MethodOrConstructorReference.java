/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.reference;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Statement;

import org.key_project.util.collection.ImmutableArray;

public interface MethodOrConstructorReference extends MemberReference, ReferencePrefix, Statement {

    /**
     * @return the array wrapper of the argument expressions .
     */
    ImmutableArray<? extends Expression> getArguments();
}
