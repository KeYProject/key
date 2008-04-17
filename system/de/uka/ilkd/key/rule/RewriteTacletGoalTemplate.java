// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.BoundVarsVisitor;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SetAsListOfSchemaVariable;
import de.uka.ilkd.key.logic.op.SetOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.SetOfSchemaVariable;

/** this class inherits from TacletGoalTemplate. It is used if there is a
 * replacewith in the ruleGoals that replaces a term by another
 * term. For a sequent {@link AntecSuccTacletGoalTemplate}
 */
public class RewriteTacletGoalTemplate extends TacletGoalTemplate {

    /** term that replaces another one */
    private Term replacewith;

    /** creates new Goaldescription 
     *@param addedSeq new Sequent to be added
     *@param addedRules ListOfTaclet contains the new allowed rules
     * at this branch 
     *@param replacewith the Term that replaces another one
     *@param pvs the set of schema variables
     */
    public RewriteTacletGoalTemplate(Sequent             addedSeq,
				     ListOfTaclet        addedRules,				     
				     Term                replacewith,
				     SetOfSchemaVariable pvs) {
	super(addedSeq, addedRules, pvs);
	TacletBuilder.checkContainsFreeVarSV(replacewith, null, "replacewith term");
	this.replacewith = replacewith;
    }

    public RewriteTacletGoalTemplate(Sequent addedSeq,
			   ListOfTaclet addedRules,
			   Term replacewith) {
	this(addedSeq, addedRules, replacewith,
	     SetAsListOfSchemaVariable.EMPTY_SET);
    }


    /** a Taclet may replace a Term by another. The new Term is returned.     
     * @return Term being paramter in the rule goal replacewith(Seq)
     */
    public Term replaceWith() {
	return replacewith;
    }
    
    /**
     * rertieves and returns all variables that are bound in the 
     * goal template
     * @return all variables that occur bound in this goal template
     */
    protected SetOfQuantifiableVariable getBoundVariables() {
        final BoundVarsVisitor bvv = new BoundVarsVisitor();
        bvv.visit(replaceWith());
        return bvv.getBoundVariables().union(super.getBoundVariables());
    }
    
    /**
     * @return Term being paramter in the rule goal replacewith(term)
     */
    Object replaceWithExpressionAsObject() {
	return replacewith;
    }


    public boolean equals(Object o) {
	if ( ! ( o instanceof RewriteTacletGoalTemplate ) )
	    return false;
	RewriteTacletGoalTemplate other = (RewriteTacletGoalTemplate) o;

	return super.equals(other)
	    && replacewith.equals(other.replacewith);
    }
    
    public int hashCode(){
    	int result = 17;
    	result = 37 * result * super.hashCode();
    	result = 37 * result * replacewith.hashCode();
    	return result;
    }

    
    /** toString */
    public String toString() {
	String result=super.toString();
	result+="\\replacewith("+replaceWith()+") ";       
	return result;
    }

}
