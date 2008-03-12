// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.visualdebugger;

import java.util.HashSet;
import java.util.List;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramConstant;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/**
 * Walks through a java AST in depth-left-fist-order. This walker is used
 * collect all ProgramVariables in a program.
 */
public class MethodVisitor extends JavaASTVisitor {

    private HashSet<ProgramVariable> result = new HashSet<ProgramVariable>();

    private List<LocalVariableDescriptor> localVariables;

    /**
     * collects all program variables occuring in the AST <tt>root</tt> using
     * this constructor is equivalent to
     * <tt>ProggramVariableCollector(root, false)</tt>
     * 
     * @param root
     *                the ProgramElement which is the root of the AST
     */
    public MethodVisitor(ProgramElement root,
            List<LocalVariableDescriptor> locVars) {
        super(root);
        this.localVariables = locVars;
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

    public HashSet<ProgramVariable> result() {
        return result;
    }

    public String toString() {
        return result.toString();
    }

    protected void doDefaultAction(SourceElement x) {
    }

    public void performActionOnProgramVariable(ProgramVariable pv) {
        // TODO realize line/column based search
        for (LocalVariableDescriptor lvd : localVariables) {
            if (pv.getProgramElementName().toString().equals(lvd.getName())) {
                // System.out.println("column myVar: " + lvd.getColumn());
                result.add(pv);
            }
        }

    }

    public void performActionOnVariableSpecification(VariableSpecification x) {
       
        System.out.println(x.getPositionInfo());
        
        System.out.println("###varSpec " + x.toSource() + ": "
                + x.getEndPosition().getLine() + " : "
                + x.getEndPosition().getColumn());

    }

    // use for catch blocks / method parameter
    public void performActionOnLocalVariableDeclaration(
            LocalVariableDeclaration x) {
        System.out.println(x.getPositionInfo());

        System.out.println("+++varDec " + x.toSource() + " col:"
                + x.getEndPosition().getLine() + " : "
                + x.getEndPosition().getColumn());
    }

    public void performActionOnLocationVariable(LocationVariable x) {
        performActionOnProgramVariable(x);
    }

    public void performActionOnProgramConstant(ProgramConstant x) {
        performActionOnProgramVariable(x);
    }

}
