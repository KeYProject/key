/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser.varexp;

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.util.Arrays;
import java.util.List;

import de.uka.ilkd.key.rule.VariableCondition;

public class ConstructorBasedBuilder extends AbstractConditionBuilder {
    private final Class<? extends VariableCondition> clazz;
    private final boolean negationSupported;

    public ConstructorBasedBuilder(String name, Class<? extends VariableCondition> clazz,
            ArgumentType... types) {
        this(name, lastArgumentOfFirstContructorIsBoolean(clazz), clazz, types);
    }

    private static boolean lastArgumentOfFirstContructorIsBoolean(
            Class<? extends VariableCondition> clazz) {
        try {
            Class<?>[] types = clazz.getConstructors()[0].getParameterTypes();
            return types[types.length - 1] == Boolean.class
                    || types[types.length - 1] == Boolean.TYPE;
        } catch (ArrayIndexOutOfBoundsException e) {
            return false;
        }
    }

    public ConstructorBasedBuilder(String name, boolean negationSupported,
            Class<? extends VariableCondition> clazz, ArgumentType... types) {
        super(name, types);
        this.clazz = clazz;
        this.negationSupported = negationSupported;
    }

    @Override
    public VariableCondition build(Object[] arguments, List<String> parameters, boolean negated) {
        if (negated && !negationSupported) {
            throw new RuntimeException(clazz.getName() + " does not support negation.");
        }

        Object[] args = arguments;
        if (negationSupported) {
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
}
