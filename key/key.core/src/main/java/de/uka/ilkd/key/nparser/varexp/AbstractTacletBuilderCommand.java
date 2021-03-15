package de.uka.ilkd.key.nparser.varexp;

import org.jetbrains.annotations.NotNull;

/**
 * Simple default implementation for {@link TacletBuilderCommand}.
 *
 * @author Alexander Weigl
 * @version 1 (12/9/19)
 */
public abstract class AbstractTacletBuilderCommand implements TacletBuilderCommand {
    private final @NotNull String triggerName;
    private final @NotNull ArgumentType[] argumentsTypes;

    /**
     * Construct this class with the parameters for {@link #isSuitableFor(String)} and {@link #getArgumentTypes()}.
     *
     * @param triggerName    the name of this command.
     * @param argumentsTypes the argument type of this command.
     */
    public AbstractTacletBuilderCommand(@NotNull String triggerName,
                                        @NotNull ArgumentType... argumentsTypes) {
        this.triggerName = triggerName;
        this.argumentsTypes = argumentsTypes;
    }

    @Override
    public boolean isSuitableFor(@NotNull String name) {
        if (triggerName.equalsIgnoreCase(name)) {
            return true;
        }
        if (name.startsWith("\\")) // handling leading backslashes
            return isSuitableFor(name.substring(1));
        return false;
    }

    @Override
    public ArgumentType[] getArgumentTypes() {
        return argumentsTypes;
    }
}
