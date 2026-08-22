/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser.varexp;

import org.jspecify.annotations.NullMarked;

/**
 * @author Alexander Weigl
 * @version 1 (12/9/19)
 */
@NullMarked
public abstract class AbstractConditionBuilder extends AbstractTacletBuilderCommand
        implements ConditionBuilder {
    protected AbstractConditionBuilder(String triggerName, ArgumentType... argumentsTypes) {
        super(triggerName, null, false, argumentsTypes);
    }

    protected AbstractConditionBuilder(
            String triggerName, Class<?> clazz, boolean isNegationSupported,
            ArgumentType... argumentsTypes) {
        super(triggerName, clazz, isNegationSupported, argumentsTypes);
    }
}
