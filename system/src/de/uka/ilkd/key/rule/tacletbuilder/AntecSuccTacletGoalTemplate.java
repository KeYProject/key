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


/** this class inherits from TacletGoalTemplate. It is used if there is a
 * replacewith in the ruleGoals that replaces a sequent with a
 * sequent. The replacewith for terms/formulae is realized in another
 * class calles RewriteTacletGoalTemplate.
*/
package de.uka.ilkd.key.rule.tacletbuilder;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.BoundVarsVisitor;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.Taclet;

public class AntecSuccTacletGoalTemplate extends TacletGoalTemplate {
    /** sequent that replaces another one */
    private Sequent replacewith=Sequent.EMPTY_SEQUENT;

    /** creates new Goaldescription 
     *@param addedSeq new Sequent to be added
     *@param addedRules IList<Taclet> contains the new allowed rules
     * at this branch 
     *@param replacewith the Sequent that replaces another one
     */
    public AntecSuccTacletGoalTemplate(Sequent addedSeq,
			   ImmutableList<Taclet> addedRules,
			   Sequent replacewith,
			   ImmutableSet<SchemaVariable> pvs) {
	super(addedSeq, addedRules, pvs);
	TacletBuilder.checkContainsFreeVarSV(replacewith, 
                null, "replacewith sequent");
	this.replacewith = replacewith;
    }

    public AntecSuccTacletGoalTemplate(Sequent addedSeq,
				     ImmutableList<Taclet> addedRules,				     
				     Sequent replacewith) {
	this(addedSeq, addedRules, replacewith,
	     DefaultImmutableSet.<SchemaVariable>nil());
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
    @Override
    public ImmutableSet<QuantifiableVariable> getBoundVariables() {
        final BoundVarsVisitor bvv = new BoundVarsVisitor();
        bvv.visit(replaceWith());
        return bvv.getBoundVariables().union(super.getBoundVariables());
    }
    
    /**
     * @return Sequent being paramter in the rule goal replacewith(Seq)
     */
    @Override
    public Object replaceWithExpressionAsObject() {
	return replacewith;
    }


    @Override
    public boolean equals(Object o) {
	if ( ! ( o instanceof AntecSuccTacletGoalTemplate ) )
	    return false;
	AntecSuccTacletGoalTemplate other = (AntecSuccTacletGoalTemplate) o;

	return super.equals(other)
	    && replacewith.equals(other.replacewith);
    }
    
    @Override
    public int hashCode(){
    	int result = 17;
    	result = 37 * result + super.hashCode();
    	result = 37 * result + replacewith.hashCode();
    	return result;
    }

    
    /** toString */
    @Override
    public String toString() {
	String result=super.toString();
	result+="\\replacewith("+replaceWith()+") ";       
	return result;
    }

}
