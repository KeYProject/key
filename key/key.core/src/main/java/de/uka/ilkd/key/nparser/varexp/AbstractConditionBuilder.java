/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
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
