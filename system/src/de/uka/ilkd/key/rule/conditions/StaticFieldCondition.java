package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class StaticFieldCondition extends VariableConditionAdapter {

    private final SchemaVariable field;
    private final boolean negated;

    public StaticFieldCondition(SchemaVariable field, boolean negated) {
        this.field = field;
        this.negated = negated;
    }

    @Override
    public boolean check(SchemaVariable var, SVSubstitute instCandidate,
                         SVInstantiations instMap, Services services) {
        Object o = instMap.getInstantiation(field);
        assert o instanceof Term;
        Term f = (Term)o;
        Operator op = f.op();
        if (op instanceof Function) {
            String name = ((Function) op).name().toString();

            String className;
            String attributeName;

            // check for normal attribute
            int endOfClassName = name.indexOf("::$");

            int startAttributeName = endOfClassName + 3;


            if ( endOfClassName < 0) {
                // not a normal attribute, maybe an implicit attribute like <created>?
                endOfClassName = name.indexOf("::<");
                startAttributeName = endOfClassName + 2;
            }

            if ( endOfClassName < 0 ) {
                return false;
            }

            className     = name.substring(0, endOfClassName);
            attributeName = name.substring(startAttributeName);

            ProgramVariable attribute =
                    services.getJavaInfo().getAttribute(attributeName, className);

            if (attribute == null) {
                return false;
            }
            final boolean result = attribute.isStatic();
            return !negated ? result : !result;
        }
        return false;
    }

    @Override
    public String toString() {
        return (negated ? "\\not":"") + "\\isStaticField(" + field + ")";
    }
}