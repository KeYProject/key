package de.uka.ilkd.key.nparser.varexp;

import org.jetbrains.annotations.NotNull;

/**
 * @author Alexander Weigl
 * @version 1 (12/9/19)
 */
public abstract class AbstractConditionBuilder implements ConditionBuilder {
    private final @NotNull String triggerName;
    private final @NotNull Class[] argumentsTypes;

    public AbstractConditionBuilder(@NotNull String triggerName, @NotNull Class... argumentsTypes) {
        this.triggerName = triggerName;
        this.argumentsTypes = argumentsTypes;
    }

    @Override
    public boolean isSuitableFor(String name) {
        return this.triggerName.equalsIgnoreCase(name);
    }

    @Override
    public Class[] getArgumentTypes() {
        return argumentsTypes;
    }
}
