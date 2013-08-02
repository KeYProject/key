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

package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.strategy.StrategyProperties;

/**
 * In the taclet language the variable condition is called "\isInductVar".
 * This variable condition checks if a logical variable is marked as an induction variable.
 * A variable is marked as such if its name has the suffix is "Ind" or "IND" and the name has length>3.
 * @author gladisch
 */
public class InductionVariableCondition extends VariableConditionAdapter {

    private final SchemaVariable arg;
    private final boolean negation;


	public InductionVariableCondition(SchemaVariable arg, boolean negation){
		this.arg = arg;
		this.negation  = negation;
	}
	
	@Override
	public boolean check(SchemaVariable var, SVSubstitute instCandidate,
			SVInstantiations instMap, Services services) {
		// TODO Auto-generated method stub
		StrategyProperties strategyProperties = services.getProof().getSettings().
		                                         getStrategySettings().getActiveStrategyProperties();
		final String queryProp = strategyProperties.getProperty(StrategyProperties.AUTO_INDUCTION_OPTIONS_KEY);
		
		if(queryProp.equals(StrategyProperties.AUTO_INDUCTION_ON) ||
		   queryProp.equals(StrategyProperties.AUTO_INDUCTION_LEMMA_ON)){
			return true;
		}
		//Otherwise auto induction is restricted or off and we check 
		//if the variable is marked as an induction variable
		
		final Term quanVar = (Term) instMap.getInstantiation(arg);
		final String name  = quanVar.toString();
		if(name.length()>3){
			final String suffix = name.substring(name.length()-3);
			if(suffix.equals("Ind") || suffix.equals("IND")){
			return true;
			}
		}
		return false;
	}
	
    @Override
    public String toString () {
	  return (negation ? " \\not " : "" ) + "\\isInductVar(" + arg + ")";
    }

}