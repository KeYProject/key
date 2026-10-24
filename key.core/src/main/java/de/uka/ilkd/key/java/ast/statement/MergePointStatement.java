/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
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

package de.uka.ilkd.key.java.ast.statement;

import java.util.List;
import java.util.Objects;

import de.uka.ilkd.key.java.ast.*;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.speclang.MergeContract;
import de.uka.ilkd.key.speclang.jml.JmlSpec;

import org.key_project.util.ExtList;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.Nullable;

/**
 * A statement indicating a merge point.
 *
 * @author Dominic Scheurer
 */
public class MergePointStatement extends JavaStatement
        implements ExpressionContainer {

    // Those are used for JML to JavaDL conversions
    protected final IProgramVariable identifier;

    private final @Nullable JmlSpec context;

    /**
     * The merge contracts belonging to this merge point, attached to the node; former
     * {@code mergeContracts} map.
     */
    private ImmutableSet<MergeContract> mergeContracts = DefaultImmutableSet.nil();

    /**
     * Returns the merge contracts belonging to this merge point.
     */
    public ImmutableSet<MergeContract> getMergeContracts() {
        return mergeContracts;
    }

    /**
     * Registers the given merge contract on this merge point.
     */
    public void addMergeContract(MergeContract contract) {
        this.mergeContracts = this.mergeContracts.add(contract);
    }

    /**
     * Deletes all merge contracts registered on this merge point.
     */
    public void removeMergeContracts() {
        this.mergeContracts = DefaultImmutableSet.nil();
    }

    @Override
    public ImmutableList<JmlSpec> getAttachedJml() {
        return context == null ? ImmutableList.nil() : ImmutableList.of(context);
    }

    public MergePointStatement(
            PositionInfo pi, List<Comment> c, @Nullable JmlSpec context,
            IProgramVariable identifier) {
        super(pi, c);
        this.identifier = identifier;
        this.context = context;
    }

    public MergePointStatement(IProgramVariable indexPV) {
        this(null, null, null, indexPV);
    }

    public MergePointStatement(ExtList children) {
        super(children);
        identifier = Objects.requireNonNull(children.get(IProgramVariable.class));
        // comments = children.get(Comment[].class);
        this.context = null;
    }

    public @Nullable JmlSpec getContext() {
        return context;
    }

    /*
     * @Override
     * public Comment[] getComments() {
     * return comments;
     * }
     */

    /**
     * Get the number of expressions in this container.
     *
     * @return the number of expressions.
     */
    public int getExpressionCount() {
        return (identifier != null) ? 1 : 0;
    }

    /**
     * Return the expression at the specified index in this node's "virtual"
     * expression array.
     *
     * @param index
     *        an index for an expression.
     * @return the expression with the given index.
     * @throws ArrayIndexOutOfBoundsException
     *         if <tt>index</tt> is out of bounds.
     */
    public Expression getExpressionAt(int index) {
        if (identifier != null && index == 0) {
            return (Expression) identifier;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get expression.
     *
     * @return the expression.
     */
    public Expression getExpression() {
        return (Expression) identifier;
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */
    public int getChildCount() {
        int result = 0;
        if (identifier != null)
            result++;
        return result;
    }

    /**
     * Returns the child at the specified index in this node's "virtual" child
     * array
     *
     * @param index
     *        an index into this node's "virtual" child array
     * @return the program element at the given position
     * @throws ArrayIndexOutOfBoundsException
     *         if <tt>index</tt> is out of bounds
     */
    public ProgramElement getChildAt(int index) {
        if (identifier != null) {
            if (index == 0)
                return identifier;
            index--;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * calls the corresponding method of a visitor in order to perform some
     * action/transformation on this element
     *
     * @param v
     *        the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnMergePointStatement(this);
    }
}
