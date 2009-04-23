// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
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
import de.uka.ilkd.key.java.declaration.Modifier;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.expression.literal.NullLiteral;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.util.ExtList;

/**
 *  A shortcut-statement for a method body.
 */
public class CatchAllStatement extends JavaNonTerminalProgramElement
    implements Statement, NonTerminalProgramElement, Desugarable, StatementContainer {

    private StatementBlock body;
    private ParameterDeclaration paramdecl;

    public CatchAllStatement(StatementBlock body, ParameterDeclaration paramdecl) {
	this.body = body;
	this.paramdecl = paramdecl;
    }
    
    public CatchAllStatement(ExtList children) {
    	super(children); // for comments
    	this.body = (StatementBlock) children.get(StatementBlock.class);
    	this.paramdecl = (ParameterDeclaration) children.get(ParameterDeclaration.class);
    }
    
    public Statement getBody() {
	return body;
    }

    public ParameterDeclaration getParameterDeclaration() {
	return paramdecl;
    }

    /**
     *      Returns the number of children of this node.
     *      @return an int giving the number of children of this node
     */
    public int getChildCount() {
	int i=0;
	if (body!=null) i++;
	if (paramdecl!=null) i++;
	return i;
    }

    public Statement getStatementAt(int i) {
        return body;
    }
    
    public int getStatementCount() {
        return 1;
    }
    
    /**
     *      Returns the child at the specified index in this node's "virtual"
     *      child array.
     *      @param index an index into this node's "virtual" child array
     *      @return the program element at the given position
     *      @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
     *                 of bounds
     */
    public ProgramElement getChildAt(int index) {
	if (index==0) {
	    return paramdecl;
	}
	if (index==1) {
	    return body;
	}	
 	throw new ArrayIndexOutOfBoundsException();
    }
    
  
    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnCatchAllStatement(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
	p.printCatchAllStatement(this);
    }

    public Object desugar() {	
        IProgramVariable pv = getParameterDeclaration()
        .getVariableSpecification().getProgramVariable();
        LocalVariableDeclaration lvd = new LocalVariableDeclaration
        (new TypeRef(pv.getKeYJavaType()),
                new VariableSpecification(pv, 0, NullLiteral.NULL, 
                        pv.getKeYJavaType()));
        ProgramVariable paramExc = new LocationVariable
        (new ProgramElementName("e"),
                pv.getKeYJavaType());
        CopyAssignment ass = new CopyAssignment((Expression)pv, paramExc);
        ParameterDeclaration parDecl 
        = new ParameterDeclaration(new Modifier[0],
                new TypeRef(pv.getKeYJavaType()),
                new VariableSpecification(paramExc),
                false);
        Catch catchBranch = new Catch(parDecl, new StatementBlock(ass));
        Try tryBlock = new Try(body, new Branch[]{catchBranch});
        return new StatementBlock(new Statement[]{lvd, tryBlock});
    }

        
}
