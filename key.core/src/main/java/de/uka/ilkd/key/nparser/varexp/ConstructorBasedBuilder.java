/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser.varexp;

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.util.Arrays;
import java.util.List;

import org.key_project.prover.rules.VariableCondition;

public class ConstructorBasedBuilder extends AbstractConditionBuilder {
    private final Class<? extends VariableCondition> clazz;

    public ConstructorBasedBuilder(String name, Class<? extends VariableCondition> clazz,
            ArgumentType... types) {
        this(TacletBuilderCommandInfo.createVarcondInfo(name, clazz, types), clazz);
    }

    public ConstructorBasedBuilder(TacletBuilderCommandInfo info,
            Class<? extends VariableCondition> clazz) {
        super(info);
        this.clazz = clazz;
    }

    @Override
    public VariableCondition build(Object[] arguments, List<String> parameters, boolean negated) {
        if (negated && !info.isNegationSupported()) {
            throw new RuntimeException(clazz.getName() + " does not support negation.");
        }

        Object[] args = arguments;
        if (info.isNegationSupported()) {
            args = Arrays.copyOf(arguments, arguments.length + 1);
            args[args.length - 1] = negated;
        }

        for (Constructor<?> constructor : clazz.getConstructors()) {
            try {
                return (VariableCondition) constructor.newInstance(args);
            } catch (InstantiationException | IllegalAccessException | InvocationTargetException
                    | IllegalArgumentException ignored) {
            }
        }
        throw new RuntimeException();
    }

    @Override
    public TacletBuilderCommandInfoImpl getInformation() {
        return (TacletBuilderCommandInfoImpl) super.getInformation();
    }
}
