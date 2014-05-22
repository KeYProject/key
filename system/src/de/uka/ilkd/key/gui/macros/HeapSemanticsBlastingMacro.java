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

/**
 * 
 */
package de.uka.ilkd.key.gui.macros;

import java.util.HashSet;
import java.util.Set;
import de.uka.ilkd.key.proof.rulefilter.RuleFilter;
import de.uka.ilkd.key.rule.Rule;

/**
 * @author bruns
 *
 */
public final class HeapSemanticsBlastingMacro extends AbstractBlastingMacro {


	private final SemanticsRuleFilter semanticsFilter;
	private final EqualityRuleFilter equalityRuleFilter;
	private final HashSet<String> allowedPullOut;
	
	public HeapSemanticsBlastingMacro() {
		super();
		semanticsFilter = new SemanticsRuleFilter();
		equalityRuleFilter = new EqualityRuleFilter();
		allowedPullOut = new HashSet<String>(); // disallow pullout
	}
	
	@Override
	protected RuleFilter getSemanticsRuleFilter () {
	    return semanticsFilter;
	}
	
	@Override
	protected RuleFilter getEqualityRuleFilter () {
	    return equalityRuleFilter;
	}
	
	@Override
	protected Set<String> getAllowedPullOut () {
	    return allowedPullOut;
	}

	@Override
	public String getName() {
		// TODO Auto-generated method stub
		return "Heap Semantics Blasting";
	}

	@Override
	public String getDescription() {
		// TODO Auto-generated method stub
		return "Semantics Blasting";
	}



	private class SemanticsRuleFilter implements RuleFilter{		
		protected HashSet<String> allowedRulesNames;		
		{
			allowedRulesNames = new HashSet<String>(40);			
			allowedRulesNames.add("selectOfStore");
			allowedRulesNames.add("selectOfCreate");
			allowedRulesNames.add("selectOfAnon");
			allowedRulesNames.add("selectOfMemset");
            
			allowedRulesNames.add("elementOfEmpty");
			allowedRulesNames.add("elementOfAllLocs");
			allowedRulesNames.add("elementOfSingleton");
			allowedRulesNames.add("elementOfUnion");
			allowedRulesNames.add("elementOfIntersect");
			allowedRulesNames.add("elementOfSetMinus");
			allowedRulesNames.add("elementOfAllFields");			
			allowedRulesNames.add("elementOfAllObjects");
			allowedRulesNames.add("elementOfArrayRange");
			allowedRulesNames.add("elementOfFreshLocs");
			allowedRulesNames.add("elementOfInfiniteUnion");
			allowedRulesNames.add("subsetToElementOf");
			allowedRulesNames.add("disjointToElementOf");
			allowedRulesNames.add("createdInHeapToElementOf");

			final HashSet<String> tmp = new HashSet<String>(20);
			for (String s: allowedRulesNames)
			    tmp.add(s+"EQ");
		}
		@Override
		public boolean filter(Rule rule) {			
			return allowedRulesNames.contains(rule.name().toString());			
		}		
	}

	private class EqualityRuleFilter implements RuleFilter{
		private HashSet<String> allowedRulesNames;		
		{
			allowedRulesNames = new HashSet<String>();			
			allowedRulesNames.add("equalityToElementOf");
			allowedRulesNames.add("equalityToSelect");
		}
		@Override
		public boolean filter(Rule rule) {			
			return allowedRulesNames.contains(rule.name().toString());			
		}
	}





}
