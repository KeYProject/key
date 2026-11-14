/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.conditions;

import java.util.Objects;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.java.ast.reference.MethodName;
import de.uka.ilkd.key.java.ast.reference.MethodReference;
import de.uka.ilkd.key.java.ast.reference.ReferencePrefix;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;


/**
 * ensures that the given instantiation for the schemavariable denotes a static method. For
 * determining the method the callee and the arguments of the method are needed as arguments.
 */
@NullMarked
public final class StaticMethodCondition extends VariableConditionAdapter {

    private final boolean negation;
    private final SchemaVariable caller;
    private final SchemaVariable methname;
    private final SchemaVariable args;

    /**
     * the static reference condition checks if a suggested instantiation for a schema variable
     * denotes a static method call. The flag negation allows to reuse this condition for ensuring
     * non static references.
     */
    public StaticMethodCondition(SchemaVariable caller, SchemaVariable methname,
            SchemaVariable args, boolean negation) {
        this.negation = negation;
        this.caller = caller;
        this.methname = methname;
        this.args = args;
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
    public boolean check(@Nullable SchemaVariable var, @Nullable SyntaxElement subst,
            SVInstantiations svInst,
            Services services) {

        ReferencePrefix rp = (ReferencePrefix) svInst.getInstantiation(caller);
        MethodName mn = (MethodName) svInst.getInstantiation(methname);
        ImmutableArray<ProgramElement> ape =
            (ImmutableArray<ProgramElement>) svInst.getInstantiation(args);

        if (rp != null && mn != null && ape != null) {
            ImmutableArray<Expression> ar = toExpArray(Objects.requireNonNull(
                (ImmutableArray<ProgramElement>) svInst.getInstantiation(args),
                "no instantiation of " + args));
            if (var == args) {
                ar = toExpArray(Objects.requireNonNull(
                    (ImmutableArray<? extends ProgramElement>) subst,
                    "no instantiation of " + args));
            }
            ExecutionContext ec = Objects.requireNonNull(svInst.getContextInstantiation(),
                "no context instantiation").activeStatementContext();
            MethodReference mr = new MethodReference(ar, mn, rp);
            IProgramMethod method = null;
            KeYJavaType prefixType =
                services.getTypeConverter().getKeYJavaType((Expression) rp, ec);
            if (rp instanceof LocationVariable locVar && locVar.sort() instanceof NullSort) {
                return true;
            }
            if (ec != null) {
                method = mr.method(services, prefixType, ec);
                // we are only interested in the signature. The method
                // must be declared in the static context.
            } else { // no execution context
                // MethodReference#getMethodSignature tolerates a null execution context (used for
                // the argument types); the parameter is still declared @NonNull there.
                @SuppressWarnings("NullAway")
                ImmutableList<KeYJavaType> signature = mr.getMethodSignature(services, ec);
                method = mr.method(services, prefixType, signature, prefixType);
            }
            if (method == null) {
                return false;
            }
            return negation ^ method.isStatic();
        }
        return true;
    }


    @Override
    public String toString() {
        return (negation ? "\\not " : "") + "\\staticMethodReference(" + caller + ", " + methname
            + ", " + args + ")";
    }
}
