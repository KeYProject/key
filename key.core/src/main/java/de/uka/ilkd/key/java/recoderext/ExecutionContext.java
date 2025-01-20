/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import de.uka.ilkd.key.java.recoderext.adt.MethodSignature;

import recoder.java.*;
import recoder.java.reference.ReferencePrefix;
import recoder.java.reference.TypeReference;
import recoder.java.reference.TypeReferenceContainer;

public class ExecutionContext extends JavaNonTerminalProgramElement
        implements Reference, TypeReferenceContainer, ExpressionContainer {

    /**
     *
     */
    private static final long serialVersionUID = 2460904042433100490L;

    /**
     * the ast parent
     */
    private NonTerminalProgramElement astParent;

    /**
     * the class context
     */
    private TypeReference classContext;

    /**
     * the method signature of the currently active method
     */
    private MethodSignature methodContext;

    /**
     * the reference to the active object
     */
    private ReferencePrefix runtimeInstance;

    protected ExecutionContext() {}

    /**
     * creates an execution context reference
     *
     * @param classContext the TypeReference referring to the next enclosing class
     * @param methodContext the method signature representing the currently active method
     * @param runtimeInstance a ReferencePrefix to the object that is currently active/executed
     */
    public ExecutionContext(TypeReference classContext, MethodSignature methodContext,
            ReferencePrefix runtimeInstance) {
        this.classContext = classContext;
        this.methodContext = methodContext;
        this.runtimeInstance = runtimeInstance;
        makeParentRoleValid();
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */
    public int getChildCount() {
        int count = 0;
        if (runtimeInstance != null) {
            count++;
        }
        if (classContext != null) {
            count++;
        }
        if (methodContext != null) {
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
     * Returns the positional code of the given child
     *
     * @param child the exact child to look for.
     * @return the positional code of the given child, or <CODE>-1</CODE>.
     */
    public int getChildPositionCode(ProgramElement child) {
        int idx = 0;
        if (classContext != null) {
            if (child == classContext) {
                return idx;
            }
            idx++;
        }
        if (methodContext != null) {
            if (child == methodContext) {
                return idx;
            }
            idx++;
        }
        if (runtimeInstance != null) {
            if (child == runtimeInstance) {
                return idx;
            }
        }
        return -1;
    }

    public void accept(SourceVisitor visitor) {
    }

    public ExecutionContext deepClone() {
        return new ExecutionContext(classContext, methodContext, runtimeInstance);
    }

    public NonTerminalProgramElement getASTParent() {
        return astParent;
    }

    public void setParent(NonTerminalProgramElement parent) {
        astParent = parent;
    }

    public boolean replaceChild(recoder.java.ProgramElement child,
            recoder.java.ProgramElement newChild) {
        if (child == classContext) {
            classContext = (TypeReference) newChild;
        } else if (child == runtimeInstance) {
            runtimeInstance = (ReferencePrefix) newChild;
        } else {
            return false;
        }
        makeParentRoleValid();
        return true;
    }

    /**
     * Ensures that each child has "this" as syntactical parent.
     */
    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (classContext != null) {
            classContext.setParent(this);
        }
        if (runtimeInstance != null) {
            ((Expression) runtimeInstance).setExpressionContainer(this);
        }
    }


    public TypeReference getTypeReferenceAt(int index) {
        if (classContext != null && index == 0) {
            return classContext;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getTypeReferenceCount() {
        return classContext == null ? 0 : 1;
    }



    public Expression getExpressionAt(int index) {
        if (runtimeInstance != null && index == 0) {
            return (Expression) runtimeInstance;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getExpressionCount() {
        return runtimeInstance == null ? 0 : 1;
    }


    /**
     * returns the type reference to the next enclosing class
     *
     * @return the type reference to the next enclosing class
     */
    public TypeReference getTypeReference() {
        return classContext;
    }

    /**
     * returns the method signature of the currently active method
     *
     * @return the method signature of the currently active method
     */
    public MethodSignature getMethodContext() {
        return methodContext;
    }


    /**
     * returns the runtime instance object
     *
     * @return the runtime instance object
     */
    public ReferencePrefix getRuntimeInstance() {
        return runtimeInstance;
    }

    public void prettyPrint(PrettyPrinter p) {
    }
}
