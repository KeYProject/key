/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression;

import recoder.java.Expression;
import recoder.java.LoopInitializer;

/**
 * An ExpressionStatement is a statement that may appear as an expression. Only one kind of parent
 * (ExpressionContainer or StatementContainer) is not null. The expression parent is more important:
 * if the expression parent is not null, the statement parent is irrelevant, if the expression
 * parent is null, the statement parent is relevant and must not be null. There are three
 * subclasses: MethodReference, Assignment, ParenthesizedExpression, and New.
 */

public interface ExpressionStatement extends Expression, LoopInitializer {
    ExpressionStatement deepClone();
}
