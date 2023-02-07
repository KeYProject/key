/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.smt.newsmt2.SMTHandlerProperty.BooleanProperty;
import de.uka.ilkd.key.smt.newsmt2.SMTHandlerProperty.EnumProperty;
import de.uka.ilkd.key.smt.newsmt2.SMTHandlerProperty.IntegerProperty;
import de.uka.ilkd.key.smt.newsmt2.SMTHandlerProperty.StringProperty;

/**
 * Visitor pattern for {@link SMTHandlerProperty} objects.
 *
 * @param <A> argument type
 * @param <R> return type
 */
public interface SMTHandlerPropertyVisitor<A, R> {
    R visit(EnumProperty<?> enumProp, A arg);

    R visit(IntegerProperty integerProp, A arg);

    R visit(BooleanProperty booleanProp, A arg);

    R visit(StringProperty stringProp, A arg);
}
