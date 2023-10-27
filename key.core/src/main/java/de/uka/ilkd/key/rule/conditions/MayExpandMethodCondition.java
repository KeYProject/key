/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import java.util.Map;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.ClassType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.recoderext.ConstructorNormalformBuilder;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.MethodName;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.util.collection.ImmutableArray;


/**
 * ensures that the given instantiation for the schemavariable denotes a method whose body may be
 * expanded. For determining the method the callee and the arguments of the method are needed as
 * arguments.
 * <p>
 * A method may be inlinded if:
 * <ul>
 * <li>the method is private, or
 * <li>the method is static, or
 * <li>the method is final, or
 * <li>the receiver class is final, or
 * <li>the corresponding taclet option is set to relaxed inlining.
 * </ul>
 *
 * @author Mattias Ulbrich, 2019
 */
public final class MayExpandMethodCondition extends VariableConditionAdapter {

    /**
     * The name of this this variable condition
     */
    public final static String NAME = "\\mayExpandMethod";

    /**
     * Name of the taclet option. Index to the choice settings
     */
    private final static String TACLET_OPTION_KEY = "methodExpansion";

    /**
     * Value of the unrestricted case. Expansion allowed unconditionally.
     */
    private final static String RELAXED_VALUE = "methodExpansion:noRestriction";

    /**
     * To indicate if this condition instance has been prefixed with "\not"
     */
    private final boolean negation;

    /**
     * Schema variable used as first argument: The receiver of the call may be null (if class local)
     */
    private final SchemaVariable receiver;

    /**
     * Schema variable used as 2nd argument: The method name
     */
    private final SchemaVariable methname;

    /**
     * Schema variable used as 3rd argument: The arguments of the call
     */
    private final SchemaVariable args;

    /**
     * Instantiate a new variable condition.
     *
     * @param negation {@code true} iff the condition is to be negated
     * @param receiver program schema var for the receiver, may be null for class-local calls
     * @param methname non-null program schema var for the methodname
     * @param args non-null program schema var for the arguments of the call
     * @param negation {@code true} iff the condition is to be negated
     */
    public MayExpandMethodCondition(SchemaVariable receiver, SchemaVariable methname,
            SchemaVariable args, boolean negation) {
        this.negation = negation;
        this.receiver = receiver;
        this.methname = methname;
        this.args = args;
    }

    public MayExpandMethodCondition(SchemaVariable methodName, SchemaVariable args,
            boolean negation) {
        this(null, methodName, args, negation);
    }

    private static ImmutableArray<Expression> toExpArray(
            ImmutableArray<? extends ProgramElement> a) {
        Expression[] result = new Expression[a.size()];
        for (int i = 0; i < a.size(); i++) {
            result[i] = (Expression) a.get(i);
        }
        return new ImmutableArray<>(result);
    }


    @SuppressWarnings("unchecked")
    @Override
    public boolean check(SchemaVariable var, SVSubstitute subst, SVInstantiations svInst,
            Services services) {
        Map<String, String> tacletOptions =
            services.getProof().getSettings().getChoiceSettings().getDefaultChoices();

        if (tacletOptions.getOrDefault(TACLET_OPTION_KEY, "").equals(RELAXED_VALUE)) {
            return !negation;
        }

        ExecutionContext ec = svInst.getContextInstantiation().activeStatementContext();
        ReferencePrefix rp = null;
        if (receiver != null) {
            rp = (ReferencePrefix) svInst.getInstantiation(receiver);
        }

        MethodName mn = (MethodName) svInst.getInstantiation(methname);

        ImmutableArray<Expression> ar =
            toExpArray((ImmutableArray<ProgramElement>) svInst.getInstantiation(args));
        if (var == args) {
            ar = toExpArray((ImmutableArray<? extends ProgramElement>) subst);
        }

        if (mn == null) {
            // unusable method name falsifies the condition
            // TODO should that perhaps raise an exception or assertion failure?
            // It should never happen. Silently ignoring may be a bad idea.
            return false;
        }

        MethodReference mr = new MethodReference(ar, mn, rp);
        IProgramMethod method;
        KeYJavaType prefixType;
        if (rp == null && ec != null) {
            // This there is no receiver, so take the context of method frame
            prefixType = ec.getTypeReference().getKeYJavaType();
        } else {
            prefixType = services.getTypeConverter().getKeYJavaType((Expression) rp, ec);
        }

        if (ec != null) {
            method = mr.method(services, prefixType, ec);
            // we are only interested in the signature. The method
            // must be declared in the static context.
        } else {
            // no execution context
            method =
                mr.method(services, prefixType, mr.getMethodSignature(services, ec), prefixType);
        }

        if (method == null) {
            return false;
        }
        return negation ^ cannotBeOverriden(method, services);
    }

    private boolean cannotBeOverriden(IProgramMethod method, Services services) {

        if (method.isStatic() || method.isPrivate() || method.isFinal()) {
            return true;
        }

        // bugfix (contributing to gitlab #1493)
        // see MethodCall.handleInstanceInvocation(...)
        if ((method.isImplicit() && method.getName()
                .equals(ConstructorNormalformBuilder.CONSTRUCTOR_NORMALFORM_IDENTIFIER))) {
            return true;
        }

        Type type = method.getContainerType().getJavaType();
        assert type instanceof ClassType
                : "Calling a method on sth that does not have a class type";

        ClassType classType = (ClassType) type;

        return classType.isFinal();
    }


    @Override
    public String toString() {
        return (negation ? "\\not " : "") + NAME + "(" + receiver + ", " + methname + ", " + args
            + ")";
    }
}
