/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.TerminalProgramElement;
import de.uka.ilkd.key.java.expression.ExpressionStatement;
import de.uka.ilkd.key.java.reference.IExecutionContext;
import de.uka.ilkd.key.java.reference.MethodName;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.Branch;
import de.uka.ilkd.key.java.statement.IForUpdates;
import de.uka.ilkd.key.java.statement.IGuard;
import de.uka.ilkd.key.java.statement.ILoopInit;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;

/**
 * A type that implement this interface can be used in all java programs instead of an expression or
 * statement. For example class SchemaVariable implements this interface to be able to stand for
 * program constructs.
 */
public interface ProgramConstruct extends Expression, Statement, ILoopInit, IForUpdates, IGuard,
        Label, TerminalProgramElement, ExpressionStatement, TypeReference, IProgramVariable,
        IProgramMethod, Branch, IExecutionContext, MethodName {
}
