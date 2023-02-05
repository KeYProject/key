package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.operator.BinaryOperator;
import de.uka.ilkd.key.java.expression.operator.TypeCast;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.visitor.ProgramElementReplacer;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.TermProgramVariableCollector;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import javax.annotation.Nullable;
import java.util.Set;


/**
 * This variable condition adds required numeric promotions to Java operations
 * with floating point arguments.
 *
 * For example: In the expression 1.0f + 1.0d, the first argument will be implicitly
 * cast to double like (double)1.0f + 1.0d.
 *
 * If such an unbalanced expression occurs in the program, according casts are
 * introduced by this varcond.
 *
 * The varcond is used like \floatingPointBalanced(#unbalanced, #balanced)
 * where the first argument is the one from the find expression of the rule
 * and the second one is the one that will be changed.
 *
 * @author Mattias Ulbrich
 * @see de.uka.ilkd.key.logic.sort.ProgramSVSort.FloatingPointBinaryExprSort
 */
public final class FloatingPointBalancedCondition implements VariableCondition {
    /**
     * The first SV: It holds the unbalanced input expression
     */
    private final SchemaVariable unbalanced;
    /**
     * The 2nd SV: It holds the balanced computed expression
     */
    private final SchemaVariable balanced;

    public FloatingPointBalancedCondition(SchemaVariable unbalanced, SchemaVariable balanced) {
        this.unbalanced = unbalanced;
        this.balanced = balanced;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SVSubstitute instCandidate, MatchConditions mc,
            Services services) {

        SVInstantiations svInst = mc.getInstantiations();
        BinaryOperator inInst = (BinaryOperator) svInst.getInstantiation(unbalanced);
        JavaProgramElement outInst = (JavaProgramElement) svInst.getInstantiation(balanced);
        if (inInst == null) {
            return mc;
        }

        BinaryOperator properResultInst = balance(inInst, services);
        if (properResultInst == null) {
            return null;
        } else if (outInst == null) {
            svInst = svInst.add(balanced, properResultInst, services);
            return mc.setInstantiations(svInst);
        } else if (outInst.equals(properResultInst)) {
            return mc;
        } else {
            return null;
        }
    }

    @Override
    public String toString() {
        return "\\floatingPointBalanced(" + unbalanced + ", " + balanced + ")";
    }

    private static KeYJavaType getKeYJavaType(ProgramElement pe, Services services) {
        return services.getTypeConverter().getKeYJavaType((Expression) pe);
    }

    /**
     * Make sure the result is a binary operation with same types on lhs
     * and rhs. do this by adding cast if needed.
     *
     * If no cast is needed, return null.
     *
     * @param inInst the binary AST element to balance
     * @param services as usual ... to lookup everything
     * @return null if already same types. Otherwise a binary operator which
     *         has an added cast compared to the input
     */
    private static @Nullable BinaryOperator balance(BinaryOperator inInst, Services services) {

        ProgramElement child0 = inInst.getChildAt(0);
        ProgramElement child1 = inInst.getChildAt(1);

        KeYJavaType type0 = getKeYJavaType(child0, services);
        KeYJavaType type1 = getKeYJavaType(child1, services);
        if (type0.getSort() == type1.getSort()) {
            // nothing to be done ... same type
            return null;
        }

        Sort doubleSort = services.getTypeConverter().getDoubleLDT().targetSort();
        Sort floatSort = services.getTypeConverter().getFloatLDT().targetSort();
        if (type0.getSort() == doubleSort) {
            return cast(inInst, 1, type0, services);
        }
        if (type1.getSort() == doubleSort) {
            return cast(inInst, 0, type1, services);
        }
        if (type0.getSort() == floatSort) {
            return cast(inInst, 1, type0, services);
        }
        if (type1.getSort() == floatSort) {
            return cast(inInst, 0, type1, services);
        }
        return null;
    }

    /**
     * Add a cast to a binary operation.
     *
     * @param inInst the tree to modify
     * @param childNo the child to which a cast is to be added
     * @param kjt the type to which to cast
     * @param services as usual
     * @return a binary operation similar to the input, but with one
     *         cast added to child childNo.
     */
    private static BinaryOperator cast(BinaryOperator inInst, int childNo, KeYJavaType kjt,
            Services services) {
        Expression child = (Expression) inInst.getChildAt(childNo);
        TypeCast cast = new TypeCast(child, new TypeRef(kjt));
        ProgramElementReplacer per = new ProgramElementReplacer(inInst, services);
        ProgramElement result = per.replace(child, cast);
        return (BinaryOperator) result;
    }
}
