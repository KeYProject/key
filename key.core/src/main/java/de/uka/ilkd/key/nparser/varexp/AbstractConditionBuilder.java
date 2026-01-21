package de.uka.ilkd.key.nparser.varexp;

import org.jspecify.annotations.NonNull;

/**
 * @author Alexander Weigl
 * @version 1 (12/9/19)
 */
public abstract class AbstractConditionBuilder extends AbstractTacletBuilderCommand
        implements ConditionBuilder {
    public AbstractConditionBuilder(@NonNull String triggerName,
            @NonNull ArgumentType... argumentsTypes) {
        super(triggerName, argumentsTypes);
    }
}
