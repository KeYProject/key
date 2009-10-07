// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//This file is part of KeY - Integrated Deductive Software Design 
//Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                      and Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License.
//See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.export;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.rule.RuleSet;



public class RuleSetModelInfo extends AbstractTacletContainer {
    private RuleSet ruleSet;
    private String definition;
    private boolean isVirtual;
    private ImmutableList<RuleSetModelInfo> intersectingSets = ImmutableSLList.<RuleSetModelInfo>nil();
    private ImmutableList<RuleSetModelInfo> superSets = ImmutableSLList.<RuleSetModelInfo>nil();
    private ImmutableList<RuleSetModelInfo> subSets = ImmutableSLList.<RuleSetModelInfo>nil();
    private ImmutableList<RuleSetModelInfo> equalSets = ImmutableSLList.<RuleSetModelInfo>nil();
    
    public RuleSetModelInfo ( RuleSet ruleSet ) {
        this.ruleSet = ruleSet;
        this.definition = null;
        this.isVirtual = false;
    }
    
    public RuleSetModelInfo ( RuleSet ruleSet, String definition, boolean isVirtual ) {
    	this.ruleSet = ruleSet;
    	this.definition = definition;
    	this.isVirtual = isVirtual;
    }
    
    public RuleSet getRuleSet () {
        return ruleSet;
    }
    
    public ImmutableList<RuleSetModelInfo> getSuperSets () {
        return superSets;
    }
    
    public void setSuperSets ( ImmutableList<RuleSetModelInfo> superSets ) {
        this.superSets = superSets;
    }
    
    public void addSuperSet ( RuleSetModelInfo set ) {
        superSets = superSets.prepend ( set );
    }
    
    public ImmutableList<RuleSetModelInfo> getEqualSets () {
        return equalSets;
    }
    
    public void setEqualSets ( ImmutableList<RuleSetModelInfo> equalRuleSets ) {
        this.equalSets = equalRuleSets;
    }
    
    public void addEqualSet ( RuleSetModelInfo set ) {
        equalSets = equalSets.prepend ( set );
    }
    
    public ImmutableList<RuleSetModelInfo> getIntersectingSets () {
        return intersectingSets;
    }
    
    public void setIntersectingSets ( ImmutableList<RuleSetModelInfo> intersectingRuleSets ) {
        this.intersectingSets = intersectingRuleSets;
    }
    
    public void addIntersectingSet ( RuleSetModelInfo set ) {
        intersectingSets = intersectingSets.prepend ( set );
    }
    
    public ImmutableList<RuleSetModelInfo> getSubSets () {
        return subSets;
    }
    
    public void setSubSets ( ImmutableList<RuleSetModelInfo> subSets ) {
        this.subSets = subSets;
    }
    
    public void addSubSet ( RuleSetModelInfo set ) {
        subSets = subSets.prepend ( set );
    }
    
    public Name name () {
        return ruleSet.name();
    }
    
    public boolean isVirtual () {
    	return isVirtual;
    }
    
    public String getDefinition() {
    	return definition;
    }
}
