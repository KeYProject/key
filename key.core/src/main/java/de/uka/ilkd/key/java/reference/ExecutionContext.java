/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.reference;

import de.uka.ilkd.key.java.JavaNonTerminalProgramElement;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Reference;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.op.IProgramMethod;

import org.key_project.util.ExtList;

public class ExecutionContext extends JavaNonTerminalProgramElement
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
    private final IProgramMethod methodContext;

    /**
     * creates an execution context reference
     *
     * @param classContext the TypeReference referring to the next enclosing class
     * @param methodContext the IProgramMethod referring to the currently active method
     * @param runtimeInstance a ReferencePrefix to the object that is currently active/executed
     */
    public ExecutionContext(TypeReference classContext, IProgramMethod methodContext,
            ReferencePrefix runtimeInstance) {
        this.classContext = classContext;
        this.methodContext = methodContext;
        this.runtimeInstance = runtimeInstance;
    }

    /**
     * creates an execution context reference
     *
     * @param children an ExtList with the required children of the execution context
     */
    public ExecutionContext(ExtList children) {
        this.classContext = children.get(TypeReference.class);
        children.remove(this.classContext);
        this.methodContext = children.get(IProgramMethod.class);
        this.runtimeInstance = children.get(ReferencePrefix.class);
    }



    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */
    @Override
    public int getChildCount() {
        int count = 0;
        if (classContext != null) {
            count++;
        }
        if (methodContext != null) {
            count++;
        }
        if (runtimeInstance != null) {
            count++;
        }
        return count;
    }

    /**
     * Returns the child at the specified index in this node's "virtual" child array.
     *
     * @param index an index into this node's "virtual" child array
     * @return the program element at the given position
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds
     */
    @Override
    public ProgramElement getChildAt(int index) {
        if (classContext != null) {
            if (index == 0) {
                return classContext;
            }
            index--;
        }
        if (methodContext != null) {
            if (index == 0) {
                return methodContext;
            }
            index--;
        }
        if (runtimeInstance != null) {
            if (index == 0) {
                return runtimeInstance;
            }
            index--;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public TypeReference getTypeReference() {
        return classContext;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public IProgramMethod getMethodContext() {
        return methodContext;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public ReferencePrefix getRuntimeInstance() {
        return runtimeInstance;
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    @Override
    public void visit(Visitor v) {
        v.performActionOnExecutionContext(this);
    }

    @Override
    public String toString() {
        return "Context: " + classContext + "#" + methodContext + " Instance: " + runtimeInstance;
    }

}
