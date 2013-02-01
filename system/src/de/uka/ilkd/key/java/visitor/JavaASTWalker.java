// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.java.visitor;

import de.uka.ilkd.key.java.NonTerminalProgramElement;
import de.uka.ilkd.key.java.ProgramElement;

/** walks through a java AST in depth-left-fist-order at default.
 * Implementing method doAction specifies its behaviour at the
 * different Nodes. The depth-left-fist behaviour can be changed by
 * overwriting the method <code> walk(ProgramElement) </code>.
 */
public abstract class JavaASTWalker {

    /** the root the walker starts */
    private ProgramElement root;

    /** the current visited level */
    private int depth = -1;

    /** create the JavaASTWalker 
     * @param root the ProgramElement where to begin
     */
    public JavaASTWalker(ProgramElement root) {
	this.root = root;
    }

    /** returns start point of the walker
     * @return root of the AST to walk through
     */
    public ProgramElement root() {
	return root;
    }

    /** starts the walker*/
    public void start() {
	walk(root);
    }

    /** 
     * returns the current vistted level
     */
    public int depth() {
	return depth;
    }

    /** walks through the AST. While keeping track of the current node
     * @param node the JavaProgramElement the walker is at 
     */
    protected void walk(ProgramElement node) {
	if(node instanceof NonTerminalProgramElement) {
	    depth++;
	    NonTerminalProgramElement nonTerminalNode = 
		(NonTerminalProgramElement) node;
	    //		System.out.println("ASTWalker - node: "+node);
	    for(int i = 0; i<nonTerminalNode.getChildCount(); i++) {
		//System.out.println("ASTWalker - node.childAt(i): "+nonTerminalNode.getChildAt(i));
		if(nonTerminalNode.getChildAt(i) != null) {
		    walk(nonTerminalNode.getChildAt(i));
		}
	    }
	    depth--;
	}
	// otherwise the node is left, so perform the action	
	doAction(node);	
    }

    /** the action that is performed just before leaving the node the
     * last time 
     */
    protected abstract void doAction(ProgramElement node);
}
