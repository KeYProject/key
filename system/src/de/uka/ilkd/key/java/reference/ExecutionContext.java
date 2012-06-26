// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.java.reference;

import de.uka.ilkd.key.java.JavaNonTerminalProgramElement;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Reference;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.util.ExtList;

public class ExecutionContext
    extends JavaNonTerminalProgramElement 
    implements IExecutionContext, Reference {
    
    /**
     * the class context 
     */
    protected final TypeReference classContext;
    
    /**
     * the reference to the active object
     */
    protected final ReferencePrefix runtimeInstance;

    /**
     * the currently active method
     */
    private ProgramMethod methodContext;
   
    /**
     * creates an execution context reference
     * @param classContext the TypeReference refering to the next enclosing
     * class 
    * @param methodContext the ProgramMethod referring to the currently active method
     * @param runtimeInstance a ReferencePrefix to the object that
     * is currently active/executed
     */
    public ExecutionContext(TypeReference classContext, 
			    ProgramMethod methodContext, ReferencePrefix runtimeInstance) {
	this.classContext = classContext;
	this.methodContext = methodContext;
	this.runtimeInstance = runtimeInstance;
    }
    
    /**
     * creates an execution context reference
     * @param children an ExtList with the required children of the execution
     * context
     */
    public ExecutionContext(ExtList children) {
	this.classContext = children.get(TypeReference.class);	
	children.remove(this.classContext);
	this.methodContext = children.get(ProgramMethod.class);
	this.runtimeInstance = children.get(ReferencePrefix.class);
    }



    /**
     * Returns the number of children of this node.
     * @return an int giving the number of children of this node
     */
    public int getChildCount() {
	int count = 0;
	if (classContext != null) count++;
   if (methodContext != null) count++;
	if (runtimeInstance != null) count++;
	return count;
    }

    /**
     * Returns the child at the specified index in this node's "virtual"
     * child array.
     * @param index an index into this node's "virtual" child array
     * @return the program element at the given position
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
     *    of bounds
     */
    public ProgramElement getChildAt(int index) {
	if (classContext != null) {
	    if (index == 0) return classContext;
	    index--;
	}
   if (methodContext != null) {
      if (index == 0) return methodContext;
      index--;
  }
	if (runtimeInstance != null) {
	    if (index == 0) return runtimeInstance;
	    index--;
	}
	throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * returns the type reference to the next enclosing class
     * @return the type reference to the next enclosing class
     */
    public TypeReference getTypeReference() {
	return classContext;
    }

    /**
     * returns the program method which is currently active
     * @return the currently active method
     */
    public ProgramMethod getMethodContext() {
      return methodContext;
   }

   /**
     * returns the runtime instance object
     * @return the runtime instance object
     */
    public ReferencePrefix getRuntimeInstance() {
	return runtimeInstance;
    }
    
    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnExecutionContext(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printExecutionContext(this);
    }

    public String toString() {
        return "Context: "+classContext+ "#" + methodContext + " Instance: "+runtimeInstance;
    }
    
}
