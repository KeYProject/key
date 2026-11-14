/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.nparser.varexp;

import org.key_project.prover.rules.VariableCondition;

/**
 * @author Alexander Weigl
 * @version 1 (12/9/19)
 */
public abstract class AbstractConditionBuilder extends AbstractTacletBuilderCommand
        implements ConditionBuilder {
    protected AbstractConditionBuilder(TacletBuilderCommandInfo info) {
        super(info);
    }

    public AbstractConditionBuilder(String name, Class<? extends VariableCondition> clazz,
            boolean negationSupported, ArgumentType... types) {
        super(TacletBuilderCommandInfo.createVarcondInfo(name, clazz, negationSupported, types));
    }
}
