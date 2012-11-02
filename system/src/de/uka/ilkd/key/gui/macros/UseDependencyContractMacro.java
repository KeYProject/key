package de.uka.ilkd.key.gui.macros;

import java.util.Set;

/**
 * The macro UseDependencyContractMacro applies all applicable dependency
 * contracts.
 * 
 * The rules that are applied can be set in {@link #ADMITTED_RULES}.
 * 
 * @author christoph
 */
public class UseDependencyContractMacro extends AbstractPropositionalExpansionMacro  {
    
    @Override 
    public String getName() {
        return "Use dependency contracts";
    }

    @Override 
    public String getDescription() {
        return "Applies all applicable dependency contract rules.";
    }

    private static final String[] ADMITTED_RULES = {
        "Use Dependency Contract"
    };

    private static final Set<String> ADMITTED_RULES_SET = asSet(ADMITTED_RULES);

    @Override
    protected Set<String> getAdmittedRuleNames() {
        return ADMITTED_RULES_SET;
    }

}
