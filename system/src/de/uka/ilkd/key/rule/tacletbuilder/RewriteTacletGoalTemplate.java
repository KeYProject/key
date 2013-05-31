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


package de.uka.ilkd.key.rule.tacletbuilder;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.BoundVarsVisitor;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.Taclet;

/** this class inherits from TacletGoalTemplate. It is used if there is a
 * replacewith in the ruleGoals that replaces a term by another
 * term. For a sequent {@link AntecSuccTacletGoalTemplate}
 */
public class RewriteTacletGoalTemplate extends TacletGoalTemplate {

    /** term that replaces another one */
    private Term replacewith;

    /** creates new Goaldescription 
     *@param addedSeq new Sequent to be added
     *@param addedRules IList<Taclet> contains the new allowed rules
     * at this branch 
     *@param replacewith the Term that replaces another one
     *@param pvs the set of schema variables
     */
    public RewriteTacletGoalTemplate(Sequent             addedSeq,
				     ImmutableList<Taclet>        addedRules,				     
				     Term                replacewith,
				     ImmutableSet<SchemaVariable> pvs) {
	super(addedSeq, addedRules, pvs);
	TacletBuilder.checkContainsFreeVarSV(replacewith, null, "replacewith term");
	this.replacewith = replacewith;
    }

    public RewriteTacletGoalTemplate(Sequent addedSeq,
			   ImmutableList<Taclet> addedRules,
			   Term replacewith) {
	this(addedSeq, addedRules, replacewith,
	     DefaultImmutableSet.<SchemaVariable>nil());
    }


    public RewriteTacletGoalTemplate(Term replacewith) {
	this(Sequent.EMPTY_SEQUENT, ImmutableSLList.<Taclet>nil(),
             replacewith);
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
    @Override
    public ImmutableSet<QuantifiableVariable> getBoundVariables() {
        final BoundVarsVisitor bvv = new BoundVarsVisitor();
        bvv.visit(replaceWith());
        return bvv.getBoundVariables().union(super.getBoundVariables());
    }
    
    /**
     * @return Term being paramter in the rule goal replacewith(term)
     */
    @Override
    public Object replaceWithExpressionAsObject() {
	return replacewith;
    }


    @Override
    public boolean equals(Object o) {
	if ( ! ( o instanceof RewriteTacletGoalTemplate ) )
	    return false;
	RewriteTacletGoalTemplate other = (RewriteTacletGoalTemplate) o;

	return super.equals(other)
	    && replacewith.equals(other.replacewith);
    }
    
    @Override
    public int hashCode(){
    	int result = 17;
    	result = 37 * result * super.hashCode();
    	result = 37 * result * replacewith.hashCode();
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
