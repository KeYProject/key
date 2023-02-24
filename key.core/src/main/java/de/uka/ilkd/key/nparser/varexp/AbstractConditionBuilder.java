package de.uka.ilkd.key.nparser.varexp;

import javax.annotation.Nonnull;

/**
 * @author Alexander Weigl
 * @version 1 (12/9/19)
 */
public abstract class AbstractConditionBuilder extends AbstractTacletBuilderCommand
        implements ConditionBuilder {
    public AbstractConditionBuilder(@Nonnull String triggerName,
            @Nonnull ArgumentType... argumentsTypes) {
        super(triggerName, argumentsTypes);
    }
}
