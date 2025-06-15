/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.smt.newsmt2.SMTHandlerProperty.BooleanProperty;
import de.uka.ilkd.key.smt.newsmt2.SMTHandlerProperty.EnumProperty;
import de.uka.ilkd.key.smt.newsmt2.SMTHandlerProperty.IntegerProperty;
import de.uka.ilkd.key.smt.newsmt2.SMTHandlerProperty.StringProperty;

import org.jspecify.annotations.Nullable;

/**
 * Visitor pattern for {@link SMTHandlerProperty} objects.
 *
 * @param <A> argument type
 * @param <R> return type
 */
public interface SMTHandlerPropertyVisitor<A, R> {
    @Nullable
    R visit(EnumProperty<?> enumProp, A arg);

    @Nullable
    R visit(IntegerProperty integerProp, A arg);

    @Nullable
    R visit(BooleanProperty booleanProp, A arg);

    @Nullable
    R visit(StringProperty stringProp, A arg);
}
