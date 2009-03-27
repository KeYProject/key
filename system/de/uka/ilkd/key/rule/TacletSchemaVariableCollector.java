// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.visitor.ProgramSVCollector;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.metaconstruct.WhileInvRule;
import de.uka.ilkd.key.rule.metaconstruct.WhileInvRuleWrapper;

/**
 * Collects all schemavariables occurring in the 
 * <code>\find, \assumes</code> part or goal description of a taclet. 
 * The addrule section is scanned optionally.      
 *  
 * Duplicates are not removed because the use of persistent
 * datastructure and up to now we just have a SetAsList-implementaion
 * causing to have O(sqr(n)) if it would used. 
 * 
 * For example, {@link de.uka.ilkd.key.rule.TacletApp} uses this class 
 * to determine all uninstantiated schemavariables.
 */
public class TacletSchemaVariableCollector extends Visitor {

    /** collects all found variables */
    protected ListOfSchemaVariable varList;
    /** the instantiations needed for unwind loop constructs */
    private SVInstantiations instantiations = 
	SVInstantiations.EMPTY_SVINSTANTIATIONS;

    /** creates the Variable collector.
     */
    public TacletSchemaVariableCollector() {
	varList = SLListOfSchemaVariable.EMPTY_LIST;
    }

    /** creates the Variable collector.
     * @param svInsts the SVInstantiations that have been already found
     * (needed by unwind loop constructs to determine which labels are needed)
     */
    public TacletSchemaVariableCollector(SVInstantiations svInsts) {
	varList = SLListOfSchemaVariable.EMPTY_LIST;
	instantiations = svInsts;
    }

    /** collects all SchemVariables that occur in the JavaBlock
     * @param jb the JavaBlock where to look for Schemavariables
     * @param vars the ListOfSchemaVariable where to add the found
     * SchemaVariables 
     * @return the extended list of found schemavariables 
     */
    protected ListOfSchemaVariable collectSVInProgram
	(JavaBlock jb, ListOfSchemaVariable vars) {

	ProgramSVCollector prgSVColl = new 
	    ProgramSVCollector(jb.program(), vars, instantiations);
	prgSVColl.start();
	return prgSVColl.getSchemaVariables();
    }

    private ListOfSchemaVariable collectSVInProgram
	(Term t, ListOfSchemaVariable vars) {

	ProgramSVCollector prgSVColl = new 
	    ProgramSVCollector(new WhileInvRuleWrapper(t), 
			       vars, instantiations);
	prgSVColl.start();
	return prgSVColl.getSchemaVariables();
    }

    private ListOfSchemaVariable collectSVInAttributeOp(AttributeOp op) {
        ListOfSchemaVariable result = SLListOfSchemaVariable.EMPTY_LIST;
        final IProgramVariable attribute = op.attribute();
        if (attribute instanceof SchemaVariable) {
             result = result.prepend((SchemaVariable)attribute);
        }
        return result;
    }
    
    /** 
     * visits the Term in post order {@link Term#execPostOrder(Visitor)} and 
     * collects all found schema variables 
     * @param t the Term whose schema variables are collected 
     */  
    public void visit(Term t) {	
	final Operator op = t.op();
        if (op instanceof Modality || 
                op instanceof ModalOperatorSV) {
	    varList = collectSVInProgram(t.javaBlock(), varList);
	} else if (op instanceof AttributeOp) {
            varList = varList.prepend(collectSVInAttributeOp((AttributeOp)op));
        } else if (op instanceof QuanUpdateOperator) {
            varList = collectSVInQuanUpdateOperator(op, varList);
        } else if (op instanceof WhileInvRule) {
 	    varList = collectSVInProgram(t, varList);
 	} else if (op instanceof SchemaVariableContainer) {
 	    varList = varList.prepend(((SchemaVariableContainer)op).collectSV(varList));
        }
        
	for (int j=0, ar = t.arity(); j<ar; j++) {
	    for (int i=0, sz = t.varsBoundHere(j).size(); i<sz; i++) {
		final QuantifiableVariable qVar = 
                    t.varsBoundHere(j).getQuantifiableVariable(i);
                if (qVar instanceof SchemaVariable) {
		    varList = varList.prepend((SchemaVariable)qVar);
		}
	    }
	}
        
        if (op instanceof SchemaVariable) {
            varList=varList.prepend((SchemaVariable)op);
        }        
    }

    /**
     * collects all schema variables occurring as part of a quantified update 
     * operator
     * @param op the {@link QuanUpdateOperator} to be scanned for schemavariables
     * @param vars the ListOfSchemaVariables with already found schema variables
     * @return a list of schema variables containing the ones of <code>vars</code> 
     *   together with the schema variables found in <code>op</code>
     */
    private ListOfSchemaVariable collectSVInQuanUpdateOperator(
            final Operator op, ListOfSchemaVariable vars) {
        ListOfSchemaVariable result = vars;
        final QuanUpdateOperator quan = (QuanUpdateOperator) op;
        for (int i = 0, locCount = quan.locationCount(); i < locCount; i++) {
            final Location currentLocation = quan.location(i);
            if (currentLocation instanceof SchemaVariable) {
                result = result.prepend((SchemaVariable) currentLocation);
            } else if (currentLocation instanceof AttributeOp) {
                result = result
                        .prepend(collectSVInAttributeOp((AttributeOp) currentLocation));
            }
        }
        return result;
    }
    
    /** @return iterator of the found Variables */
    public IteratorOfSchemaVariable varIterator() {
	return varList.iterator();
    }

    /** @return number of the found variables */
    public int size() {
	return varList.size();
    }

    /** @return true iff term contains the given variable */
    public boolean contains(SchemaVariable var) {
	return varList.contains(var);
    }

   
    
    /** collects all variables in a Semisequent 
     * @param semiseq the Semisequent to visit
     */
    private void visit(Semisequent semiseq) {
	IteratorOfConstrainedFormula it=semiseq.iterator();
	while(it.hasNext()) {
	    it.next().formula().execPostOrder(this);
	}
    }

    /** goes through the given sequent an collects all vars found
     * @param seq the Sequent to visit
     */
    public void visit(Sequent seq) {
	visit(seq.antecedent());
	visit(seq.succedent());
    }

    /** 
     * collects all schema variables of a taclet
     * @param taclet the Taclet where the variables have to be collected to
     * @param visitAddrules a boolean that contols if the addrule sections are
     * to be ignored (iff false) or if the visitor descends into them (iff true) 
     */
    public void visit(Taclet taclet, boolean visitAddrules) {
	visit(taclet.ifSequent());
        visitFindPart(taclet);
        visitGoalTemplates(taclet, visitAddrules);
    }
    
    
    protected void visitFindPart(Taclet taclet) {
	if (taclet instanceof FindTaclet) {
	    (((FindTaclet)taclet).find()).execPostOrder(this);
	}	
    }
    
    
    protected void visitGoalTemplates(Taclet taclet, boolean visitAddrules) {
	IteratorOfTacletGoalTemplate it = taclet.goalTemplates().iterator();
	while (it.hasNext()) {
	    TacletGoalTemplate gt=it.next();
	    visit(gt.sequent());
	    if (gt instanceof RewriteTacletGoalTemplate) {
		((RewriteTacletGoalTemplate)gt).replaceWith().execPostOrder(this);
	    } else {
		if(gt instanceof AntecSuccTacletGoalTemplate) {
		    visit(((AntecSuccTacletGoalTemplate)gt).replaceWith());
		}
	    }
	    if (visitAddrules) {
		IteratorOfTaclet addruleIt = gt.rules().iterator();
		while (addruleIt.hasNext()) {
		    visit(addruleIt.next(), true);		    
		}
	    }
	}
    }


    /** collects all variables in a Taclet but ignores the variables that appear
     * only in the addrule sections of the Taclet
     * @param taclet the Taclet where the variables have to be collected to
     */
    public void visitWithoutAddrule(Taclet taclet) {
	visit(taclet, false);
    }
    
}
