/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
// Universitaet Koblenz-Landau, Germany
// Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
// Technical University Darmstadt, Germany
// Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.ast.reference;

import java.util.List;

import de.uka.ilkd.key.java.ast.*;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.op.IProgramMethod;

import org.key_project.util.ExtList;

public class ExecutionContext
        extends JavaNonTerminalProgramElement
        implements IExecutionContext, Reference {
    protected final TypeReference classContext;
    /**
     * the reference to the active object
     */
    protected final ReferencePrefix runtimeInstance;

    /**
     * the currently active method
     */
    private final IProgramMethod methodContext;

    public ExecutionContext(
            PositionInfo pi, List<Comment> comments, TypeReference classContext,
            ReferencePrefix runtimeInstance, IProgramMethod methodContext) {
        super(pi, comments);
        this.classContext = classContext;
        this.runtimeInstance = runtimeInstance;
        this.methodContext = methodContext;
    }

    /**
     * creates an execution context reference
     *
     * @param classContext
     *        the TypeReference referring to the next enclosing
     *        class
     * @param methodContext
     *        the IProgramMethod referring to the currently active method
     * @param runtimeInstance
     *        a ReferencePrefix to the object that
     *        is currently active/executed
     */
    public ExecutionContext(TypeReference classContext, IProgramMethod methodContext,
            ReferencePrefix runtimeInstance) {
        this(null, null, classContext, runtimeInstance, methodContext);
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */
    @Override
    public int getChildCount() {
        int count = 0;
        if (classContext != null)
            count++;
        if (methodContext != null)
            count++;
        if (runtimeInstance != null)
            count++;
        return count;
    }

    /**
     * Returns the child at the specified index in this node's "virtual"
     * child array.
     *
     * @param index
     *        an index into this node's "virtual" child array
     * @return the program element at the given position
     * @exception ArrayIndexOutOfBoundsException
     *            if <tt>index</tt> is out
     *            of bounds
     */
    @Override
    public ProgramElement getChildAt(int index) {
        if (classContext != null) {
            if (index == 0)
                return classContext;
            index--;
        }
        if (methodContext != null) {
            if (index == 0)
                return methodContext;
            index--;
        }
        if (runtimeInstance != null) {
            if (index == 0)
                return runtimeInstance;
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
     * calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     *
     * @param v
     *        the Visitor
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
