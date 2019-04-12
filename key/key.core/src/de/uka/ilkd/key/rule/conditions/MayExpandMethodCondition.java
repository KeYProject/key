// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.ClassType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.MethodName;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import org.key_project.util.collection.ImmutableArray;

import java.util.Map;
import java.util.Set;


/**
 * ensures that the given instantiation for the schemavariable denotes
 * a method whose body may be expanded. For determining the method the callee and the
 * arguments of the method are needed as arguments.
 * <p>
 * A method may be inlinded if: <ul>
 * <li>the method is private, or
 * <li>the method is static, or
 * <li>the method is final, or
 * <li>the receiver class is final, or
 * <li>the corresponding taclet option is set to relaxed inlining.
 * </ul>
 */
public final class MayExpandMethodCondition extends VariableConditionAdapter {

    private final static String TACLET_OPTION_KEY = "methodExpansion";
    private final static String RELAXED_VALUE = "methodExpansion:noRestriction";
    public final static String NAME = "\\mayExpandMethod";

    private final boolean negation;
    private final SchemaVariable caller;
    private final SchemaVariable methname;
    private final SchemaVariable args;

    /**
     * Instantiate a new variable condition.
     *
     * @param negation {@code true} iff the condition is to be negated
     * @param caller program schema var for the receiver, may be null for class-local calls
     * @param methname non-null program schema var for the methodname
     * @param args non-null program schema var for the arguments of the call
     */
    public MayExpandMethodCondition(boolean negation,
                                    SchemaVariable caller,
                                    SchemaVariable methname,
                                    SchemaVariable args) {
        this.negation = negation;
        this.caller = caller;
        this.methname = methname;
        this.args = args;
    }

    private static ImmutableArray<Expression> toExpArray(ImmutableArray<? extends ProgramElement> a) {
        Expression[] result = new Expression[a.size()];
        for (int i=0; i<a.size(); i++) {
            result[i]=(Expression)a.get(i);
        }
        return new ImmutableArray<Expression>(result);
    }


    @SuppressWarnings("unchecked")
    @Override
    public boolean check(SchemaVariable var,
                         SVSubstitute subst,
                         SVInstantiations svInst,
                         Services services) {

        Map<String, String> tacletOptions = services.getProof().getSettings().
                getChoiceSettings().getDefaultChoices();

        if (tacletOptions.getOrDefault(TACLET_OPTION_KEY, "").equals(RELAXED_VALUE)) {
            return !negation;
        }

        ExecutionContext ec = svInst.getContextInstantiation().activeStatementContext();
        ReferencePrefix rp;
        if (caller == null) {
            rp = ec.getRuntimeInstance();
        } else {
            rp = (ReferencePrefix) svInst.getInstantiation(caller);
        }

        MethodName mn = (MethodName) svInst.getInstantiation(methname);
        ImmutableArray<ProgramElement> ape =
                (ImmutableArray<ProgramElement>) svInst.getInstantiation(args);

        ImmutableArray<Expression> ar =
                toExpArray((ImmutableArray<ProgramElement>)svInst.getInstantiation(args));
        if (var == args) {
            ar = toExpArray((ImmutableArray<? extends ProgramElement>)subst);
        }

        MethodReference mr = new MethodReference(ar, mn, rp);
        IProgramMethod method;
        KeYJavaType prefixType = services.getTypeConverter().getKeYJavaType((Expression) rp, ec);
        if (ec!=null) {
            method = mr.method(services, prefixType, ec);
            // we are only interested in the signature. The method
            // must be declared in the static context.
        } else { //no execution context
            method = mr.method (services, prefixType, mr.getMethodSignature(services, ec), prefixType);
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

        Type type = method.getContainerType().getJavaType();
        assert type instanceof ClassType : "Calling a method on sth that does not have a class type";
        ClassType classType = (ClassType) type;
        if (classType.isFinal()) {
            return true;
        }

        return false;
    }


    @Override
    public String toString () {
        return (negation ? "\\not " : "") + NAME + "(" + caller
                + ", " + methname + ", " + args + ")";
    }
}