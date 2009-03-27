// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.visualdebugger.executiontree;

import java.util.LinkedList;

import de.uka.ilkd.key.logic.ListOfTerm;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ListOfProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramMethod;

/**
 * An instance of this specialised node class is used if a node in an execution
 * tree refers to an invocation of a method. In these cases it is useful to
 * extract and cache additional information for later inspection like
 * <ul>
 * <li> the invoked method (after dynamic dispatch) </li>
 * <li> parameter names and their values</li>
 * </ul>
 * 
 * FIXME: the copy method creates insane trees (I do currently no understand
 * what ITNodes are, but most probably the copy method brings ETNodes and
 * ITNodes out of sync), up to now I am not sure which behaviour of copy has
 * been wanted. This bug applies to all subclasses as well.
 */
public class ETMethodInvocationNode extends ETNode {

    /** the method that has been invoked */
    private final ProgramMethod method;

    /**
     * TODDO don't know yet why and if necessary to keep this
     */
    private final Term methodReference;

    /**
     * the program variables representing the methods parameters TODO: check if
     * order is the same as in method signature and if yes comment it here!
     */
    private final ListOfProgramVariable parameters;

    /**
     * the values of the parameters at the point of method invocation
     */
    private final ListOfTerm values;

    /**
     * creates an execution tree node referring to a method invocation
     * 
     * @param bc
     *                TODO ???
     * @param itNodes
     *                TODO ???
     * @param method
     *                the ProgramMethod which is invoked
     * @param methodReference
     *                TODO ????
     * @param parameters
     *                ListOfProgramVariable enumerating the method parameters
     * @param values
     *                ListOfTerm enumerating the values of the paramters at the
     *                time when the method invocation occurred
     * @param parent
     *                the direct ancestor node of this node
     */
    public ETMethodInvocationNode(ListOfTerm bc, LinkedList itNodes,
            ProgramMethod method, Term methodReference,
            ListOfProgramVariable parameters, ListOfTerm values, ETNode parent) {
        super(bc, itNodes, parent);
        this.method = method;
        this.methodReference = methodReference;
        this.parameters = parameters;
        this.values = values;

    }

    /**
     * creates an execution tree node referring to a method invocation
     * 
     * @param bc
     *                TODO ???
     * @param method
     *                the ProgramMethod which is invoked
     * @param methodReference
     *                TODO ????
     * @param parameters
     *                ListOfProgramVariable enumerating the method parameters
     * @param values
     *                ListOfTerm enumerating the values of the paramters at the
     *                time when the method invocation occurred
     * @param parent
     *                the direct ancestor node of this node
     */
    public ETMethodInvocationNode(ListOfTerm bc, ProgramMethod method,
            Term methodReference, ListOfProgramVariable parameters,
            ListOfTerm values, ETNode parent) {
        super(bc, parent);
        this.method = method;
        this.methodReference = methodReference;
        this.parameters = parameters;
        this.values = values;
    }

    /**
     * returns the invoked method
     * 
     * @return the ProgramMethod representing the invoked method
     */
    public ProgramMethod getMethod() {
        return method;
    }

    public Term getMethodReference() {
        return methodReference;
    }

    /**
     * the program variables representing the method parameters
     * 
     * @return the program variables representing the method parameters
     */
    public ListOfProgramVariable getParameters() {
        return parameters;
    }

    /**
     * the symbolic values of the method paramters
     * 
     * @return the symbolic values of the method parameters
     */
    public ListOfTerm getValues() {
        return values;
    }

    /**
     * creates a shallow copy of this node and attaches it to node <tt>p</tt>
     * FIXME: FIX this method as it creates not well linked trees Problems: 1)
     * the children of this node are not linked to their new parent -->
     * malformed tree 2) the children are not copied themselves and linking
     * would destroy the old tree
     * 
     */
    public ETNode copy(ETNode p) {
        final ETMethodInvocationNode copy = new ETMethodInvocationNode(this
                .getBC(), (LinkedList) this.getITNodes().clone(), this.method,
                this.methodReference, this.parameters, this.values, p);
        copy.setChildren((LinkedList) this.getChildrenList().clone());
        return copy;
    }

}
