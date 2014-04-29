// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

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

/** A type that implement this interface can be used in all java
 * programs instead of an expression or statement. For example class
 * SchemaVariable implements this interface to be able to stand for
 * program constructs.
 */
public interface ProgramConstruct extends Expression, Statement, ILoopInit, 
    IForUpdates, IGuard, Label, TerminalProgramElement, ExpressionStatement,
    TypeReference, IProgramVariable, IProgramMethod, Branch, IExecutionContext, MethodName {  
}