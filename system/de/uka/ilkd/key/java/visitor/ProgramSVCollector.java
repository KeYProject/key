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
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.logic.op.ListOfSchemaVariable;
import de.uka.ilkd.key.logic.op.SLListOfSchemaVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.metaconstruct.MetaConstructWithSV;

/** 
 * This visitor is used to collect all appearing SchemaVariables in a 
 * java program
 */
public class ProgramSVCollector extends JavaASTWalker {

    private ListOfSchemaVariable result = 
	SLListOfSchemaVariable.EMPTY_LIST; 

    /** the instantiations needed for unwind loop constructs */
    private SVInstantiations instantiations = 
	SVInstantiations.EMPTY_SVINSTANTIATIONS;

    /** create the ProgramSVCollector
     * @param root the ProgramElement where to begin
     * @param vars the ListOfSchemaVariable where to add the new found
     * ones
     */
    public ProgramSVCollector(ProgramElement root, 
			      ListOfSchemaVariable vars) {
	super(root);
	result = vars;
    }

    /** create the ProgramSVCollector
     * @param root the ProgramElement where to begin
     * @param vars the ListOfSchemaVariable where to add the new found
     * ones
     * @param svInst the SVInstantiations previously found in order to determine
     * the needed labels for the UnwindLoop construct. 
     */
    public ProgramSVCollector(ProgramElement root, 
			      ListOfSchemaVariable vars,
			      SVInstantiations svInst) {
	super(root);
	result = vars;
	instantiations = svInst;
    }

    /** starts the walker*/
    public void start() {
	walk(root());
    }

    public ListOfSchemaVariable getSchemaVariables() {
	return result;
    }

    /** 
     * the action that is performed just before leaving the node the last time.
     * Not only schema variables must be taken into consideration, but also
     * program meta constructs with implicit schema variables containment
     * 
     * @see MetaConstructWithSV
     */
    protected void doAction(ProgramElement node) {
	// System.out.println("bbbbbbbbbbbbbbb "+node+(node instanceof
	// WhileInvRuleWrapper));
	if (node instanceof SchemaVariable) {
	    result = result.prepend((SchemaVariable) node);
	} else if (node instanceof MetaConstructWithSV) {
	    MetaConstructWithSV mc = (MetaConstructWithSV)node;
	    result = result.prepend(mc.neededInstantiations(instantiations));
	}
    }
}
