// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 



package de.uka.ilkd.key.java.reference;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.util.ExtList;



public class VariableReference extends JavaNonTerminalProgramElement
                               implements  NameReference, Expression, 
                               ReferencePrefix {

    protected final ProgramVariable variable;
    
    protected VariableReference() {
        variable = null;
    }

    public VariableReference(ExtList children) {
	super(children);	
	variable=children.get(ProgramVariable.class);
    }

    public VariableReference(ProgramVariable variable, PositionInfo pi) {
	super(pi);
	this.variable = variable;
    }

    public VariableReference(ProgramVariable variable) {
	this(variable, PositionInfo.UNDEFINED);
    }


    public ProgramElementName getProgramElementName(){
	return (ProgramElementName) variable.name();
    }

    public int getChildCount() {
        return (variable != null) ? 1 : 0;
    }

    /**
     * Returns the child at the specified index in this node's "virtual"
     * child array
     * @param index an index into this node's "virtual" child array
     * @return the program element at the given position
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
     *  of bounds
     */
    public ProgramElement getChildAt(int index) {
        if (variable != null) {
            if (index == 0) return variable;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public ProgramElementName getIdentifier(){
	return (ProgramElementName) variable.name();
    }

    
    public final String getName() {
        return (variable == null) ? null : variable.toString();
    }


    public ProgramVariable getProgramVariable() {
        return variable;
    }

    public SourceElement getFirstElement() {
        return variable;
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
	variable.prettyPrint(p);
    }

    /** 
     * calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnVariableReference(this);
    }

    /**
     * We do not have a prefix, so fake it!
     * This way we implement ReferencePrefix
     * @author VK
     */
    public ReferencePrefix getReferencePrefix() {
	return null;
    }

    public ReferencePrefix setReferencePrefix(ReferencePrefix r) {
	return this;
    }

    public KeYJavaType getKeYJavaType(Services javaServ, 
				      ExecutionContext ec) {
	return getKeYJavaType();
    }

    public KeYJavaType getKeYJavaType(Services javaServ) {
	return getKeYJavaType();
    }

    public KeYJavaType getKeYJavaType() {
	return variable != null? variable.getKeYJavaType() : null;
    }
}
