package de.uka.ilkd.key.nparser.varexp;

import org.jetbrains.annotations.NotNull;

/**
 * @author Alexander Weigl
 * @version 1 (12/9/19)
 */
public abstract class AbstractTacletBuilderCommand implements TacletBuilderCommand {
    private final @NotNull String triggerName;
    private final @NotNull ArgumentType[] argumentsTypes;

    public AbstractTacletBuilderCommand(@NotNull String triggerName,
                                        @NotNull ArgumentType... argumentsTypes) {
        this.triggerName = triggerName;
        this.argumentsTypes = argumentsTypes;
    }

    @Override
    public boolean isSuitableFor(String name) {
        if (triggerName.equalsIgnoreCase(name)) {
            return true;
        }
        if (name.startsWith("\\"))
            return isSuitableFor(name.substring(1));
        return false;
    }

    @Override
    public ArgumentType[] getArgumentTypes() {
        return argumentsTypes;
    }
}
