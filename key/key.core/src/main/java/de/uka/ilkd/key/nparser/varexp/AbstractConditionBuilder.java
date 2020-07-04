package de.uka.ilkd.key.nparser.varexp;

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
