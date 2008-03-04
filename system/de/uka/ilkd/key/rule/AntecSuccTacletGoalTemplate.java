// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

/** this class inherits from TacletGoalTemplate. It is used if there is a
 * replacewith in the ruleGoals that replaces a sequent with a
 * sequent. The replacewith for terms/formulae is realized in another
 * class calles RewriteTacletGoalTemplate.
*/
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.BoundVarsVisitor;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.op.SetAsListOfSchemaVariable;
import de.uka.ilkd.key.logic.op.SetOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.SetOfSchemaVariable;

public class AntecSuccTacletGoalTemplate extends TacletGoalTemplate{
    /** sequent that replaces another one */
    private Sequent replacewith=Sequent.EMPTY_SEQUENT;

    /** creates new Goaldescription 
     *@param addedSeq new Sequent to be added
     *@param addedRules ListOfTaclet contains the new allowed rules
     * at this branch 
     *@param replacewith the Sequent that replaces another one
     */
    public AntecSuccTacletGoalTemplate(Sequent addedSeq,
			   ListOfTaclet addedRules,
			   Sequent replacewith,
			   SetOfSchemaVariable pvs) {
	super(addedSeq, addedRules, pvs);
	TacletBuilder.checkContainsFreeVarSV(replacewith, 
                null, "replacewith sequent");
	this.replacewith = replacewith;
    }

    public AntecSuccTacletGoalTemplate(Sequent addedSeq,
				     ListOfTaclet addedRules,				     
				     Sequent replacewith) {
	this(addedSeq, addedRules, replacewith,
	     SetAsListOfSchemaVariable.EMPTY_SET);
    }

    /** a Taclet may replace a Sequent by another. The new Sequent is returned.
     * this Sequent.
     * @return Sequent being paramter in the rule goal replacewith(Seq)
     */
    public Sequent replaceWith() {
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
     * @return Sequent being paramter in the rule goal replacewith(Seq)
     */
    Object replaceWithExpressionAsObject() {
	return replacewith;
    }


    public boolean equals(Object o) {
	if ( ! ( o instanceof AntecSuccTacletGoalTemplate ) )
	    return false;
	AntecSuccTacletGoalTemplate other = (AntecSuccTacletGoalTemplate) o;

	return super.equals(other)
	    && replacewith.equals(other.replacewith);
    }
    
    public int hashCode(){
    	int result = 17;
    	result = 37 * result + super.hashCode();
    	result = 37 * result + replacewith.hashCode();
    	return result;
    }

    
    /** toString */
    public String toString() {
	String result=super.toString();
	result+="\\replacewith("+replaceWith()+") ";       
	return result;
    }

}
