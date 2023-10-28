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
import java.util.Objects;


import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.ast.*;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import org.jspecify.annotations.NonNull;


public class VariableReference extends JavaNonTerminalProgramElement
        implements NameReference, Expression, ReferencePrefix {

    @NonNull
    protected final ProgramVariable variable;

    public VariableReference(PositionInfo pi, List<Comment> comments,
            @NonNull ProgramVariable variable) {
        super(pi, comments);
        this.variable = Objects.requireNonNull(variable);
    }

    public VariableReference(@NonNull ProgramVariable variable, PositionInfo pi) {
        super(pi);
        this.variable = Objects.requireNonNull(variable);
    }

    public VariableReference(@NonNull ProgramVariable variable) {
        this(variable, PositionInfo.UNDEFINED);
    }


    public ProgramElementName getProgramElementName() {
        return (ProgramElementName) variable.name();
    }

    public int getChildCount() {
        return (variable != null) ? 1 : 0;
    }

    /**
     * Returns the child at the specified index in this node's "virtual"
     * child array
     *
     * @param index an index into this node's "virtual" child array
     * @return the program element at the given position
     * @throws ArrayIndexOutOfBoundsException if <tt>index</tt> is out
     *         of bounds
     */
    public ProgramElement getChildAt(int index) {
        if (variable != null) {
            if (index == 0) {
                return variable;
            }
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public ProgramElementName getIdentifier() {
        return (ProgramElementName) variable.name();
    }


    public final String getName() {
        return (variable == null) ? null : variable.toString();
    }


    public ProgramVariable getProgramVariable() {
        return variable;
    }

    @NonNull
    public SourceElement getFirstElement() {
        return variable;
    }

    /**
     * calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnVariableReference(this);
    }

    /**
     * We do not have a prefix, so fake it!
     * This way we implement ReferencePrefix
     *
     * @author VK
     */
    public ReferencePrefix getReferencePrefix() {
        return null;
    }

    public ReferencePrefix setReferencePrefix(ReferencePrefix r) {
        return this;
    }

    /**
     * Gets the KeY java type.
     *
     * @param javaServ the java services
     * @param ec the execution context
     * @return the KeY java type
     */
    public KeYJavaType getKeYJavaType(Services javaServ,
            ExecutionContext ec) {
        return getKeYJavaType();
    }

    public KeYJavaType getKeYJavaType(Services javaServ) {
        return getKeYJavaType();
    }

    public KeYJavaType getKeYJavaType() {
        return variable != null ? variable.getKeYJavaType() : null;
    }
}
