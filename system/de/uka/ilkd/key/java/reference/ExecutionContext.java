// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
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
import de.uka.ilkd.key.util.Debug;
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
     * the current memory area
     */
    protected final ReferencePrefix memoryArea;
    
    /**
     * PERC Pico specific: the memory area for creating the returned object in
     */
    protected final ReferencePrefix callerMemoryArea;
    
    /**
     * PERC Pico specific: the constructed memory area
     */
    protected final ReferencePrefix constructedMemoryArea;
    
    /**
     * creates an execution context reference
     * @param classContext the TypeReference refering to the next enclosing
     * class 
     * @param memoryArea the memory area used for allocation within this execution
     * context
     * @param runtimeInstance a ReferencePrefix to the object that
     * is currently active/executed
     */
    public ExecutionContext(TypeReference classContext, 
            ReferencePrefix memoryArea,
            ReferencePrefix runtimeInstance) {
        this(classContext, memoryArea, runtimeInstance, null, null); 
    }
    
   
    /**
     * creates an execution context reference
     * @param classContext the TypeReference refering to the next enclosing
     * class 
     * @param memoryArea the memory area used for allocation within this execution
     * context
     * @param runtimeInstance a ReferencePrefix to the object that
     * is currently active/executed
     * @param callerMemoryArea the memory area used for allocation of the returned
     * object (PERC Pico)
     * @param constructedMemoryArea the constructed scope (PERC Pico)
     */
    public ExecutionContext(TypeReference classContext, 
            ReferencePrefix memoryArea,
            ReferencePrefix runtimeInstance,
            ReferencePrefix callerMemoryArea,
            ReferencePrefix constructedMemoryArea) {
        if (classContext == null) Debug.printStackTrace();
        this.classContext = classContext;
        this.runtimeInstance = runtimeInstance;
        this.memoryArea = memoryArea;
        this.callerMemoryArea = callerMemoryArea; 
        this.constructedMemoryArea = constructedMemoryArea; 
    }
    
    /**
     * creates an execution context reference
     * @param children an ExtList with the required children of the execution
     * context
     */
    public ExecutionContext(ExtList children) {
	this.classContext = (TypeReference) children.get(TypeReference.class);	
	if (classContext == null)
	    { System.out.println("||||"+children); Debug.printStackTrace(); }

	children.remove(this.classContext);
        this.memoryArea = (ReferencePrefix) children.removeFirstOccurrence(
                ReferencePrefix.class); 
        this.callerMemoryArea = (ReferencePrefix) children.removeFirstOccurrence(
                ReferencePrefix.class); 
        this.constructedMemoryArea = (ReferencePrefix) children.removeFirstOccurrence(
                ReferencePrefix.class); 
        this.runtimeInstance = (ReferencePrefix) children.removeFirstOccurrence(
                ReferencePrefix.class);
    }



    /**
     * Returns the number of children of this node.
     * @return an int giving the number of children of this node
     */
    public int getChildCount() {
	int count = 0;
	if (classContext != null) count++;
        if (memoryArea != null) count++;
        if (runtimeInstance != null) count++;
        if (constructedMemoryArea != null) count++;
        if (callerMemoryArea != null) count++;
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
	if (memoryArea != null) {
	    if (index == 0) return memoryArea;
	    index--;
	}
        if (callerMemoryArea != null) {
            if (index == 0) return callerMemoryArea;
            index--;
        }
        if (constructedMemoryArea != null) {
            if (index == 0) return constructedMemoryArea;
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
     * returns the runtime instance object
     * @return the runtime instance object
     */
    public ReferencePrefix getRuntimeInstance() {
	return runtimeInstance;
    }
    
    public ReferencePrefix getMemoryArea() {
        return memoryArea;
    }
    
    public ReferencePrefix getConstructedMemoryArea() {
        return constructedMemoryArea;
    }
    
    public ReferencePrefix getCallerMemoryArea() {
        return callerMemoryArea;
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
        return "Context: "+classContext+" MemoryArea: "+memoryArea+
        " CallerMemoryArea: "+callerMemoryArea+
        " ConstructedMemoryArea: "+constructedMemoryArea+
        " Instance: "+runtimeInstance;
    }
    
}
