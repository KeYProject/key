package de.uka.ilkd.key.nparser.varexp;

import de.uka.ilkd.key.rule.VariableCondition;

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;

public class ConstructorBasedBuilder extends AbstractConditionBuilder {
    private final Class<? extends VariableCondition> clazz;
    private final boolean negationSupported;

    public ConstructorBasedBuilder(String name, Class<? extends VariableCondition> clazz, ArgumentType... types) {
        this(name, true, clazz, types);
    }

    public ConstructorBasedBuilder(String name, boolean negationSupported, Class<? extends VariableCondition> clazz, ArgumentType... types) {
        super(name, types);
        this.clazz = clazz;
        this.negationSupported = negationSupported;
    }

    @Override
    public VariableCondition build(Object[] arguments, boolean negated) {
        if (!negated && !negationSupported) {
            throw new RuntimeException();
        }

        for (Constructor<?> constructor : clazz.getConstructors()) {
            try {
                return (VariableCondition) constructor.newInstance(arguments);
            } catch (InstantiationException | IllegalAccessException | InvocationTargetException ignored) {
            }
        }
        throw new RuntimeException();
    }
}
