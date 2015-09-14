// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.util.joinrule;

import de.uka.ilkd.key.java.NonTerminalProgramElement;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.visitor.JavaASTWalker;

/**
 * Walks through the Java AST of two program elements simultaneously in
 * depth-left-fist-order at default. Implementing method doAction specifies its
 * behavior at the different Nodes. The depth-left-fist behavior can be changed
 * by overwriting the method <code>walk(ProgramElement)</code>.
 *
 * @see JavaASTWalker
 * @author Dominic Scheurer
 */
public abstract class SimultaneousJavaASTWalker {

    /** The roots where the walker starts. */
    private ProgramElement e1, e2;

    /** The currently visited level. */
    private int depth = -1;

    /** True iff the given program elements have a different structure. */
    private boolean incompatible = false;

    /**
     * Create the SimultaneousJavaASTWalker.
     * 
     * @param e1
     *            The first ProgramElement to start with.
     * @param e2
     *            The second ProgramElement to start with.
     */
    public SimultaneousJavaASTWalker(ProgramElement e1, ProgramElement e2) {
        this.e1 = e1;
        this.e2 = e2;
    }

    /**
     * Returns the first start point of the walker.
     * 
     * @return First root of the AST to walk through.
     */
    public ProgramElement getFirstRoot() {
        return e1;
    }

    /**
     * Returns the second start point of the walker.
     * 
     * @return Second root of the AST to walk through.
     */
    public ProgramElement getSecondRoot() {
        return e2;
    }

    /**
     * @return True iff the given program elements are incompatible (that is,
     *         differ in more than just the naming of the program variables).
     */
    public boolean isIncompatible() {
        return incompatible;
    }

    /**
     * @param incompatible
     *            Call iff the given program elements are incompatible
     *            (that is, differ in more than just the naming of the program
     *            variables).
     */
    public void setIncompatible() {
        this.incompatible = true;
    }

    /** Starts the walker. */
    public void start() {
        walk(e1, e2);
    }

    /**
     * @return The currently visited level.
     */
    public int depth() {
        return depth;
    }

    /**
     * Walks through the ASTs simultaneously, while keeping track of the current
     * nodes.
     * 
     * @param node1
     *            The first JavaProgramElement the walker is at.
     * @param node2
     *            The second JavaProgramElement the walker is at.
     */
    protected void walk(ProgramElement node1, ProgramElement node2) {
        if (node1 == null || node2 == null
                || !node1.getClass().equals(node2.getClass())) {
            setIncompatible();
        }
        else {

            if (node1 instanceof NonTerminalProgramElement) {
                depth++;

                NonTerminalProgramElement nonTerminalNode1 = (NonTerminalProgramElement) node1;
                NonTerminalProgramElement nonTerminalNode2 = (NonTerminalProgramElement) node2;

                if (nonTerminalNode1.getChildCount() != nonTerminalNode2
                        .getChildCount()) {
                    setIncompatible();
                    return;
                }

                for (int i = 0; i < nonTerminalNode1.getChildCount(); i++) {
                    walk(nonTerminalNode1.getChildAt(i),
                            nonTerminalNode2.getChildAt(i));
                }

                depth--;
            }

            // otherwise the node is left, so perform the action
            doAction(node1, node2);

        }
    }

    /**
     * The action that is performed just before leaving the node the last time.
     */
    protected abstract void doAction(ProgramElement node1, ProgramElement node2);
}