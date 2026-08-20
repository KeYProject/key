/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser.varexp;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Simple default implementation for {@link TacletBuilderCommand}.
 *
 * @author Alexander Weigl
 * @version 1 (12/9/19)
 */
@NullMarked
public abstract class AbstractTacletBuilderCommand implements TacletBuilderCommand {
    private final String triggerName;
    private final ArgumentType[] argumentsTypes;
    private final @Nullable Class<?> clazz;
    private final boolean isNegationSupported;

    /**
     * Construct this class with the parameters for {@link #isSuitableFor(String)} and
     * {@link #getArgumentTypes()}.
     *
     * @param triggerName the name of this command.
     * @param argumentsTypes the argument type of this command.
     */
    protected AbstractTacletBuilderCommand(String triggerName, Class<?> clazz,
            boolean isNegationSupported,
            ArgumentType... argumentsTypes) {
        this.triggerName = triggerName;
        this.clazz = clazz;
        this.isNegationSupported = isNegationSupported;
        this.argumentsTypes = argumentsTypes;
    }

    protected AbstractTacletBuilderCommand(String triggerName,
            ArgumentType... argumentsTypes) {
        this(triggerName, null, false, argumentsTypes);
    }

    @Override
    public boolean isSuitableFor(String name) {
        if (triggerName.equalsIgnoreCase(name)) {
            return true;
        }
        if (name.startsWith("\\")) // handling leading backslashes
        {
            return isSuitableFor(name.substring(1));
        }
        return false;
    }

    @Override
    public ArgumentType[] getArgumentTypes() {
        return argumentsTypes;
    }

    @Override
    public String getTriggerName() {
        return triggerName;
    }


    @Override
    public @Nullable Class<?> getRelevantClazz() {
        return clazz;
    }

    @Override
    public boolean isNegationSupported() {
        return isNegationSupported;
    }
}
