package de.uka.ilkd.key.nparser.varexp;

import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.tacletbuilder.TacletBuilder;

import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (12/10/19)
 */
public interface ConditionBuilder extends TacletBuilderCommand {
    VariableCondition build(Object[] arguments, List<String> parameters, boolean negated);

    @Override
    public default void apply(TacletBuilder<?> tacletBuilder, Object[] arguments, List<String> parameters, boolean negated) {
        VariableCondition condition = build(arguments, parameters, negated);
        tacletBuilder.addVariableCondition(condition);
    }
}
