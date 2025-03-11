/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.newsmt2;

/**
 * Writeable objects have the possibility to be written to a {@link StringBuilder}.
 * <p>
 * This avoids to explicitly invoke {@link Object#toString()} on larger objects which might be
 * inefficient.
 * </p>
 * <p>
 * Most prominent subclass is {@link SExpr}.
 * </p>
 *
 * @author Mattias Ulbrich
 *
 * @see SExpr
 * @see VerbatimSMT
 */
public interface Writable {
    void appendTo(StringBuilder sb);
}
