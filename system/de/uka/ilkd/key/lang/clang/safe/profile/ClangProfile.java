package de.uka.ilkd.key.lang.clang.safe.profile;

import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.lang.clang.safe.services.ClangSafeServices;
import de.uka.ilkd.key.lang.common.services.ILangServices;
import de.uka.ilkd.key.lang.common.services.ILangServicesEnv;
import de.uka.ilkd.key.proof.SetOfGoalChooserBuilder;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.mgt.ComplexRuleJustification;
import de.uka.ilkd.key.proof.mgt.ComplexRuleJustificationBySpec;
import de.uka.ilkd.key.proof.mgt.RuleJustification;
import de.uka.ilkd.key.rule.ListOfBuiltInRule;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.UpdateSimplificationRule;
import de.uka.ilkd.key.rule.UseMethodContractRule;
import de.uka.ilkd.key.strategy.FOLStrategy;
import de.uka.ilkd.key.strategy.SetOfStrategyFactory;
import de.uka.ilkd.key.strategy.StrategyFactory;

/**
 * This profile sets up KeY for verification of C programs with Safe C Dynamic Logic (CDL).
 * 
 * @author oleg.myrk@gmail.com
 */
public class ClangProfile extends AbstractProfile {

	private final static StrategyFactory DEFAULT = new ClangDLStrategy.Factory();

	protected ClangProfile(String standardRules, SetOfGoalChooserBuilder gcb,
			Main main) {
		super(standardRules, gcb, main);
	}

	protected ClangProfile(String standardRules, Main main) {
		super(standardRules, main);
	}

	public ClangProfile() {
		this(null);
	}

	public ClangProfile(Main main) {
		this("lang/clang/safe/profiles/profile_NoBit.key", main);
	}

	protected SetOfStrategyFactory getStrategyFactories() {
		SetOfStrategyFactory set = super.getStrategyFactories();
		set = set.add(DEFAULT);
		set = set.add(new FOLStrategy.Factory());
		return set;
	}

	protected UseMethodContractRule getContractRule() {
		return UseMethodContractRule.INSTANCE;
	}

	protected UpdateSimplificationRule getUpdateSimplificationRule() {
		return UpdateSimplificationRule.INSTANCE;
	}

	protected ListOfBuiltInRule initBuiltInRules() {
		// update simplifier
		ListOfBuiltInRule builtInRules = super.initBuiltInRules().prepend(
				getUpdateSimplificationRule());

		// contract insertion rule, ATTENTION: ProofMgt relies on the fact
		// that Contract insertion rule is the FIRST element of this list!
		builtInRules = builtInRules.prepend(getContractRule());

		return builtInRules;
	}

	/**
	 * determines the justification of rule <code>r</code>. For a method
	 * contract rule it returns a new instance of a
	 * {@link ComplexRuleJustification} otherwise the rule justification
	 * determined by the super class is returned
	 * 
	 * @return justification for the given rule
	 */
	public RuleJustification getJustification(Rule r) {
		return r == getContractRule() ? new ComplexRuleJustificationBySpec()
				: super.getJustification(r);
	}

	/**
	 * the name of the profile
	 */
	public String name() {
		return "Clang Profile";
	}

	/**
	 * the default strategy factory to be used
	 */
	public StrategyFactory getDefaultStrategyFactory() {
		return DEFAULT;
	}
             
	/**
	 * Returns C langauge services.
         * @param env environment to use
	 */
        public ILangServices getLanguageServices(ILangServicesEnv env) {
                return new ClangSafeServices(env);
        }
}
