// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.

package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.POBrowser;
import de.uka.ilkd.key.proof.init.proofobligation.DefaultPOProvider;
import de.uka.ilkd.key.proof.mgt.ComplexRuleJustification;
import de.uka.ilkd.key.proof.mgt.ComplexRuleJustificationBySpec;
import de.uka.ilkd.key.proof.mgt.RuleJustification;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.UpdateSimplificationRule;
import de.uka.ilkd.key.rule.UseOperationContractRule;
import de.uka.ilkd.key.strategy.FOLStrategy;
import de.uka.ilkd.key.strategy.JavaCardDLStrategy;
import de.uka.ilkd.key.strategy.StrategyFactory;


/**
 * This profile is only used by test cases written for and to test KeY.
 */
public class JUnitTestProfile extends AbstractProfile {

    private final static StrategyFactory DEFAULT =
        new JavaCardDLStrategy.Factory();


    public JUnitTestProfile() {
        super("standardRules-junit.key", null);
    }


    protected ImmutableSet<StrategyFactory> getStrategyFactories() {
        ImmutableSet<StrategyFactory> set = super.getStrategyFactories();
        set = set.add(DEFAULT);
        set = set.add(new FOLStrategy.Factory());
        return set;
    }

    protected UseOperationContractRule getContractRule() {
        return UseOperationContractRule.INSTANCE;
    }

    protected UpdateSimplificationRule getUpdateSimplificationRule() {
        return UpdateSimplificationRule.INSTANCE;
    }

    protected ImmutableList<BuiltInRule> initBuiltInRules() {

        // update simplifier
        ImmutableList<BuiltInRule> builtInRules = super.initBuiltInRules().
            prepend(getUpdateSimplificationRule());

        //contract insertion rule, ATTENTION: ProofMgt relies on the fact
        // that Contract insertion rule is the FIRST element of this list!
        builtInRules = builtInRules.prepend(getContractRule());

        return builtInRules;
    }

    /**
     * determines the justification of rule <code>r</code>. For a method contract rule it
     * returns a new instance of a {@link ComplexRuleJustification} otherwise the rule
     * justification determined by the super class is returned
     *
     * @return justification for the given rule
     */
    public RuleJustification getJustification(Rule r) {
        return r == getContractRule() ? new ComplexRuleJustificationBySpec() :
            super.getJustification(r);
    }

    /**
     * the name of the profile
     */
    public String name() {
        return "Profile For JUnit Tests";
    }

    /**
     * the default strategy factory to be used
     */
    public StrategyFactory getDefaultStrategyFactory() {
        return DEFAULT;
    }

    /**
     * returns the file name of the internal class list
     * @return the file name of the internal class list
     */
    public String getInternalClasslistFilename() {
	 return "JAVALANGTESTGEN.TXT";
    }

    public DefaultPOProvider getPOProvider() {
	return new DefaultPOProvider();
    }


    public Class<POBrowser> getPOBrowserClass() {
	return POBrowser.class;
    }

}
