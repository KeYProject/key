package de.uka.ilkd.key.nparser.varexp;

import de.uka.ilkd.key.rule.tacletbuilder.TacletBuilder;
import org.jetbrains.annotations.NotNull;

/**
 * @author Alexander Weigl
 * @version 1 (12/9/19)
 */
public abstract class AbstractConditionBuilder
        extends AbstractTacletBuilderCommand
        implements ConditionBuilder {
    public AbstractConditionBuilder(@NotNull String triggerName, @NotNull ArgumentType... argumentsTypes) {
        super(triggerName, argumentsTypes);
    }
}
