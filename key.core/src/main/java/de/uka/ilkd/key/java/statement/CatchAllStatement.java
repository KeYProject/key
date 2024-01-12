/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.op.LocationVariable;

import org.key_project.util.ExtList;



public class CatchAllStatement extends JavaNonTerminalProgramElement
        implements Statement, NonTerminalProgramElement, StatementContainer {
    private final StatementBlock body;
    private final LocationVariable param;

    public CatchAllStatement(StatementBlock body, LocationVariable param) {
        this.body = body;
        this.param = param;
    }


    public CatchAllStatement(ExtList children) {
        super(children); // for comments
        this.body = children.get(StatementBlock.class);
        this.param = children.get(LocationVariable.class);
    }


    public Statement getBody() {
        return body;
    }


    public LocationVariable getParam() {
        return param;
    }


    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */
    public int getChildCount() {
        int i = 0;
        if (body != null) {
            i++;
        }
        if (param != null) {
            i++;
        }
        return i;
    }


    public Statement getStatementAt(int i) {
        return body;
    }


    public int getStatementCount() {
        return 1;
    }


    /**
     * Returns the child at the specified index in this node's "virtual" child array.
     *
     * @param index an index into this node's "virtual" child array
     * @return the program element at the given position
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds
     */
    public ProgramElement getChildAt(int index) {
        if (index == 0) {
            return param;
        }
        if (index == 1) {
            return body;
        }
        throw new ArrayIndexOutOfBoundsException();
    }


    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnCatchAllStatement(this);
    }


    // public Object desugar() {
    // IProgramVariable pv = getParameterDeclaration()
    // .getVariableSpecification().getProgramVariable();
    // LocalVariableDeclaration lvd = new LocalVariableDeclaration
    // (new TypeRef(pv.getKeYJavaType()),
    // new VariableSpecification(pv, 0, NullLiteral.NULL,
    // pv.getKeYJavaType()));
    // ProgramVariable paramExc = new LocationVariable
    // (new ProgramElementName("e"),
    // pv.getKeYJavaType());
    // CopyAssignment ass = new CopyAssignment((Expression)pv, paramExc);
    // ParameterDeclaration parDecl
    // = new ParameterDeclaration(new Modifier[0],
    // new TypeRef(pv.getKeYJavaType()),
    // new VariableSpecification(paramExc),
    // false);
    // Catch catchBranch = new Catch(parDecl, new StatementBlock(ass));
    // Try tryBlock = new Try(body, new Branch[]{catchBranch});
    // return new StatementBlock(new Statement[]{lvd, tryBlock});
    // }
}
