package de.uka.ilkd.key.nparser.varexp;

import de.uka.ilkd.key.logic.op.FormulaSV;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.conditions.SameObserverCondition;
import de.uka.ilkd.key.rule.conditions.SimplifyIfThenElseUpdateCondition;
import de.uka.ilkd.key.rule.conditions.StaticFieldCondition;
import de.uka.ilkd.key.rule.conditions.SubFormulaCondition;

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

/**
 * @author Alexander Weigl
 * @version 1 (12/9/19)
 */
public class CommonConditionBuilders {
    static Map<String, ConditionBuilder> builders = new TreeMap<>();
    private static Class<?> PV = ParsableVariable.class;
    public static AbstractConditionBuilder SAME_OBSERVER
            = new ConstructorBasedBuilder("sameObserver", SameObserverCondition.class, PV, PV);
    private static Class<?> SV = SchemaVariable.class;
    private static Class<?> USV = UpdateSV.class;
    private static Class<?> FSV = FormulaSV.class;
    public static AbstractConditionBuilder SIMPLIFY_ITE_UPDATE
            = new ConstructorBasedBuilder("simplifyIfThenElseUpdate", SimplifyIfThenElseUpdateCondition.class,
            FSV, USV, USV, FSV, SV);
    public static AbstractConditionBuilder SUBFORMULAS = new ConstructorBasedBuilder("subFormulas", SubFormulaCondition.class, FSV);
    public static AbstractConditionBuilder STATIC_FIELD = new ConstructorBasedBuilder("staticField", StaticFieldCondition.class, FSV);


    static {
        register(SAME_OBSERVER, SIMPLIFY_ITE_UPDATE);
    }

    public static void register(ConditionBuilder... cb) {
        for (ConditionBuilder a : cb) {
            register(a);
        }
    }

    public static void register(ConditionBuilder cb) {
    }


    public static List<ConditionBuilder> getConditionBuilders() {
        return null;
    }

    private static class ConstructorBasedBuilder extends AbstractConditionBuilder {
        private final Class<? extends VariableCondition> clazz;
        private final boolean negationSupported;

        public ConstructorBasedBuilder(String name, Class<? extends VariableCondition> clazz, Class... types) {
            this(name, true, clazz, types);
        }

        public ConstructorBasedBuilder(String name, boolean negationSupported, Class<? extends VariableCondition> clazz, Class... types) {
            super(name, types);
            this.clazz = clazz;
            this.negationSupported = negationSupported;
        }


        public ConstructorBasedBuilder(String name, Class<? extends VariableCondition> clazz, boolean negationSupported) {
            this(name, negationSupported, clazz, clazz.getConstructors()[0].getParameterTypes());
        }


        public ConstructorBasedBuilder(String name, Class<? extends VariableCondition> clazz) {
            this(name, clazz, true);
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
}