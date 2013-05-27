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

package de.uka.ilkd.key.rule.metaconstruct;


import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.QueryExpand;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.strategy.StrategyProperties;


/**
 * Uses the class <code>QueryExpand</code> in order to insert query expansions in the term that the
 * meta construct is applied on.
 * @author gladisch
 */
public class ExpandQueriesMetaConstruct extends AbstractTermTransformer {

	public static final String name= "#ExpandQueries";

    public ExpandQueriesMetaConstruct() {
    	super(new Name(name), 2, Sort.FORMULA);
    }

/** term.sub(0) is the term that possibly contains queries.
 *  term.sub(1) is expected to be true or false. True indicates that the
 *  meta construct appears in a positive context wrt. to logical negation, (e.g. in the succedent or negated in the antecedent)
 *  False implies means that the meta construct appears in a negative context. (e.g. in the antecedent or negated in the succedent)
 */
   public Term transform(Term term, SVInstantiations svInst, Services services) {
    	Term arg1 = term.sub(0);
    	Term arg2 = term.sub(1); //true or false. If true, than the application of the meta construct
    	boolean positiveContext;
    	if(arg2.op() == Junctor.TRUE){
    		positiveContext = true;
    	}else if (arg2.op() == Junctor.FALSE){
    		positiveContext = false;
    	}else {
    		throw new RuntimeException("Second argument of the meta construct "+name+ " must be true or false, but it is: "+arg2);
    	}

    	final Term result;
    	final StrategyProperties props = services.getProof().getSettings().getStrategySettings().getActiveStrategyProperties();
    	final boolean queryTreatmenIsOn = props.getProperty(StrategyProperties.QUERY_OPTIONS_KEY)==StrategyProperties.QUERY_ON;
    	if(queryTreatmenIsOn ||
    	   props.getProperty(StrategyProperties.QUERY_OPTIONS_KEY)==StrategyProperties.QUERY_RESTRICTED){
    		result = QueryExpand.INSTANCE.evaluateQueries(services, arg1, positiveContext, queryTreatmenIsOn);
   	}else{
    		result = arg1;
    	}
    	return result;
   }

}