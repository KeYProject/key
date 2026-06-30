/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser.varexp;

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.util.Arrays;
import java.util.List;

import org.key_project.prover.rules.VariableCondition;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class ConstructorBasedBuilder extends AbstractConditionBuilder {

    private static final Logger LOGGER = LoggerFactory.getLogger(ConstructorBasedBuilder.class);
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
                LOGGER.debug("Constructor " + constructor
                    + " does not match the given arguments for VariableCondition " + clazz
                    + ". Trying next constructor.");
            }
        }

        throw new RuntimeException(
            "No matching constructor found for VariableCondition " + clazz + " with args "
                + Arrays.toString(args));
    }
}
