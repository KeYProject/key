// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.visualdebugger.watchpoints;

import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramConstant;

/**
 * Walks through a java AST in depth-left-first-order. This walker is used
 * collect all ProgramVariables in a program.
 */
public class MethodVisitor extends JavaASTVisitor {

    private Map<SourceElement, Integer> keyPositions = new HashMap<SourceElement, Integer>();

    private int count = 0;

    /**
     * collects all program variables occuring in the AST <tt>root</tt> using
     * this constructor is equivalent to
     * <tt>ProggramVariableCollector(root, false)</tt>
     * 
     * @param root
     *                the method which is the root of the AST that is to be visited
     * @param services
     *                the Services
     */
    public MethodVisitor(ProgramElement root, Services services) {
        super(root, services);
    }

    /**
     * the action that is performed just before leaving the node the last time
     */
    protected void doAction(ProgramElement node) {
        node.visit(this);
    }

    /** starts the walker */
    public void start() {
        walk(root());
    }

    public Map<SourceElement, Integer> result() {
        return keyPositions;
    }

    public String toString() {
        return keyPositions.toString();
    }

    protected void doDefaultAction(SourceElement x) {
    }

    public void performActionOnVariableSpecification(VariableSpecification x) {
        keyPositions.put(x, count++);
    }

    public void performActionOnLocationVariable(LocationVariable x) {
        performActionOnProgramVariable(x);
    }

    public void performActionOnProgramConstant(ProgramConstant x) {
        performActionOnProgramVariable(x);
    }

}
