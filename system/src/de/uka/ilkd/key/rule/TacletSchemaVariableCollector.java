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

package de.uka.ilkd.key.rule;

import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.visitor.ProgramSVCollector;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.Visitor;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.ModalOperatorSV;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.tacletbuilder.AntecSuccTacletGoalTemplate;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;

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
public class TacletSchemaVariableCollector extends DefaultVisitor {

    /** collects all found variables */
    protected ImmutableList<SchemaVariable> varList;
    /** the instantiations needed for unwind loop constructs */
    private SVInstantiations instantiations = 
	SVInstantiations.EMPTY_SVINSTANTIATIONS;


    public TacletSchemaVariableCollector() {
	varList = ImmutableSLList.<SchemaVariable>nil();
    }

    
    /**
     * @param svInsts the SVInstantiations that have been already found
     * (needed by unwind loop constructs to determine which labels are needed)
     */
    public TacletSchemaVariableCollector(SVInstantiations svInsts) {
	varList = ImmutableSLList.<SchemaVariable>nil();
	instantiations = svInsts;
    }

    
    /** collects all SchemVariables that occur in the JavaBlock
     * @param jb the JavaBlock where to look for Schemavariables
     * @param vars the IList<SchemaVariable> where to add the found
     * SchemaVariables 
     * @return the extended list of found schemavariables 
     */
    protected ImmutableList<SchemaVariable> collectSVInProgram
	(JavaBlock jb, ImmutableList<SchemaVariable> vars) {

	ProgramSVCollector prgSVColl = new 
	    ProgramSVCollector(jb.program(), vars, instantiations);
	prgSVColl.start();
	return prgSVColl.getSchemaVariables();
    }
    
    
    /** 
     * visits the Term in post order {@link Term#execPostOrder(Visitor)} and 
     * collects all found schema variables 
     * @param t the Term whose schema variables are collected 
     */  
    @Override
    public void visit(Term t) {	
	final Operator op = t.op();
        if (op instanceof Modality || 
                op instanceof ModalOperatorSV) {
	    varList = collectSVInProgram(t.javaBlock(), varList);
	} else if (op instanceof ElementaryUpdate) {
            varList = collectSVInElementaryUpdate((ElementaryUpdate)op, varList);
        } 
        
	for (int j=0, ar = t.arity(); j<ar; j++) {
	    for (int i=0, sz = t.varsBoundHere(j).size(); i<sz; i++) {
		final QuantifiableVariable qVar = 
                    t.varsBoundHere(j).get(i);
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
     * collects all schema variables occurring on the lhs of an elementary update
     * @param op the ElementaryUpdate operator to be scanned for schemavariables
     * @param vars the ImmutableList<SchemaVariable> with already found schema variables
     * @return a list of schema variables containing the ones of <code>vars</code> 
     *   together with the schema variables found in <code>op</code>
     */
    private ImmutableList<SchemaVariable> collectSVInElementaryUpdate(
	    	ElementaryUpdate op, 
	    	ImmutableList<SchemaVariable> vars) {
        ImmutableList<SchemaVariable> result = vars;
        
        if(op.lhs() instanceof SchemaVariable) {
            result = result.prepend((SchemaVariable) op.lhs());
        }

        return result;
    }
    
    /** @return list of found Variables */
    public Iterable<SchemaVariable> vars() {
   return varList;
    }
    
    /** @return iterator of the found Variables */
    public Iterator<SchemaVariable> varIterator() {
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
        for (SequentFormula aSemiseq : semiseq) {
            aSemiseq.formula().execPostOrder(this);
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
        for (TacletGoalTemplate tacletGoalTemplate : taclet.goalTemplates()) {
            TacletGoalTemplate gt = tacletGoalTemplate;
            visit(gt.sequent());
            if (gt instanceof RewriteTacletGoalTemplate) {
                ((RewriteTacletGoalTemplate) gt).replaceWith().execPostOrder(this);
            } else {
                if (gt instanceof AntecSuccTacletGoalTemplate) {
                    visit(((AntecSuccTacletGoalTemplate) gt).replaceWith());
                }
            }
            if (visitAddrules) {
                for (Taclet taclet1 : gt.rules()) {
                    visit(taclet1, true);
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