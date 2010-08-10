// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.visitor.CreatingASTVisitor;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;

/**
 * The new enhanced form of a for-loop.
 * 
 * for(Type var : exp) Statement
 * 
 * LoopStatement.inits is initialized with "Type var" LoopStatement.guard is
 * initialized with "exp" LoopStatement.body with "statement"
 * 
 * @author mulbrich
 */
public class EnhancedFor extends LoopStatement implements VariableScope {

    /**
     * create empty for loop.
     */
    public EnhancedFor() {
    }

    /**
     * Used for the Recoder2KeY transformation.
     * 
     * @param init
     *            the initializers - here a single VariableDeclaration. may not be null.
     * @param guard
     *            a guard - here an expression of type Iterable. may not be null.
     * @param statement
     *            the statement of the loop
     * @param comments
     *            collected comments
     * @param info
     *            position
     */
    public EnhancedFor(LoopInit init, Guard guard, Statement statement,
            ExtList comments, PositionInfo info) {
        super(init, guard, null, statement, comments, info);
        assert init != null;
        assert guard != null;
    }

    /**
     * Used by the {@link CreatingASTVisitor}.
     * 
     * @param children a list of parameters
     */
    public EnhancedFor(ExtList children) {
        super((ILoopInit) children.get(ILoopInit.class), (IGuard) children
                .get(IGuard.class), null, (Statement) children
                .get(Statement.class), children);
    }

    /**
     * @see de.uka.ilkd.key.java.statement.For#getLastElement()
     * @see de.uka.ilkd.key.java.JavaSourceElement#getLastElement()
     */
    public SourceElement getLastElement() {
        return (body != null) ? body.getLastElement() : this;
    }

    /**
     * @see de.uka.ilkd.key.java.statement.For#isExitCondition()
     * @see recoder.java.statement.LoopStatement#isExitCondition()
     */
    public boolean isExitCondition() {
        // TODO (?)
        return false;
    }

    /**
     * @see de.uka.ilkd.key.java.statement.For#isCheckedBeforeIteration
     * @see recoder.java.statement.LoopStatement#isCheckedBeforeIteration()
     */
    public boolean isCheckedBeforeIteration() {
        // TODO (?)
        return true;
    }

    public void visit(Visitor v) {
        v.performActionOnEnhancedFor(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printEnhancedFor(this);
    }
    
    /**
     * get the local variable declaration of the enhanced for-loop
     * <code>for(type var : exp)</code> gives <code>type var</code>.
     * @return the local variable declaration.
     */
    public LocalVariableDeclaration getVariableDeclaration() {
        return (LocalVariableDeclaration)getInitializers().get(0);
    }

}
