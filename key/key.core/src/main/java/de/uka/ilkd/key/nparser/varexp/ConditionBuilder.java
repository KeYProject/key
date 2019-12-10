package de.uka.ilkd.key.nparser.varexp;

import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.tacletbuilder.TacletBuilder;

/**
 * @author Alexander Weigl
 * @version 1 (12/10/19)
 */
public interface ConditionBuilder extends TacletBuilderCommand {
    VariableCondition build(Object[] arguments, boolean negated);

    @Override
    public default void build(TacletBuilder tacletBuilder, Object[] arguments, boolean negated) {
        VariableCondition condition = build(arguments, negated);
        tacletBuilder.addVariableCondition(condition);
    }
}
