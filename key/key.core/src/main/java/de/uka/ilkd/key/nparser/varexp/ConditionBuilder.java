package de.uka.ilkd.key.nparser.varexp;

import de.uka.ilkd.key.rule.VariableCondition;

/**
 * @author Alexander Weigl
 * @version 1 (12/9/19)
 */
public interface ConditionBuilder {
    public boolean isSuitableFor(String name);
    public Class[] getArgumentTypes();
    public VariableCondition build(Object[] arguments, boolean negated);
}
