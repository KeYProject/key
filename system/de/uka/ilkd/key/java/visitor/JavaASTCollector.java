// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.java.visitor;

import de.uka.ilkd.key.java.ListOfProgramElement;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.SLListOfProgramElement;
/** Walks through a java AST in depth-left-fist-order. 
 * You can set the type of nodes you want to collect and then start the
 * walker. The found nodes of the given type are returned as a 
 * ListOfJavaProgramElement
 */
public class JavaASTCollector extends JavaASTWalker {

    /** the type of nodes to be collected */
    private Class type;
    /** the list of found elements */
    private ListOfProgramElement resultList = 
	SLListOfProgramElement.EMPTY_LIST;

    /** create the JavaASTWalker 
     * @param root the ProgramElement where to begin
     * @param type the Class representing the type of nodes that have
     * to be collected
     */
    public JavaASTCollector(ProgramElement root, Class type) {
	super(root);
	this.type = type;
    }

    /** the action that is performed just before leaving the node the
     * last time 
     */
    protected void doAction(ProgramElement node) {
	if (type.isInstance(node)) {
	    resultList = resultList.prepend(node);
	}
    }

    /** returns the found nodes of the specified type
     * @return the found nodes of the specified type as list
     */
    public ListOfProgramElement getNodes() {
	return resultList;
    }

}
