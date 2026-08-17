/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.ldt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.expression.Operator;
import de.uka.ilkd.key.java.ast.expression.literal.Literal;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.ParametricFunctionDecl;

import org.key_project.logic.Name;
import org.key_project.logic.Named;
import org.key_project.logic.Namespace;
import org.key_project.logic.op.Function;
import org.key_project.util.ExtList;

import org.jspecify.annotations.Nullable;

public abstract class AbstractLDT implements Named {
    protected final Name name;

    /// the namespace of functions this LDT feels responsible for
    private final Namespace<Function> functions = new Namespace<>();
    /// the namespace of parametric functions this LDT feels responsible for
    private final Namespace<ParametricFunctionDecl> parametricFunctions = new Namespace<>();


    protected AbstractLDT(Name name) {
        this.name = name;
    }

    /// adds a function to the LDT
    ///
    /// @return the added function (for convenience reasons)
    protected final Function addFunction(Function f) {
        functions.addSafely(f);
        return f;
    }

    /// adds a parametric function to the LDT
    ///
    /// @return the added parametric function (for convenience reasons)
    protected final ParametricFunctionDecl addParametricFunction(ParametricFunctionDecl f) {
        parametricFunctions.addSafely(f);
        return f;
    }

    /// looks up a function in the namespace and adds it to the LDT
    ///
    /// @param funcName the String with the name of the function to look up
    /// @return the added function (for convenience reasons)
    protected final <F extends Function> F addFunction(TermServices services, String funcName) {
        final Namespace<Function> funcNS = services.getNamespaces().functions();
        final Function f = funcNS.lookup(new Name(funcName));
        if (f == null) {
            throw new RuntimeException("LDT: Function " + funcName + " not found.\n"
                + "It seems that there are definitions missing from the .key files.");
        }
        return (F) addFunction(f);
    }

    protected final ParametricFunctionDecl addParametricFunction(TermServices services,
            String name) {
        final ParametricFunctionDecl f =
            services.getNamespaces().parametricFunctions().lookup(name);
        assert f != null : "LDT: Parametric function " + name + " not found";
        return addParametricFunction(f);
    }

    /// returns the basic functions of the model
    ///
    /// @return the basic functions of the model
    protected final Namespace<Function> functions() {
        return functions;
    }

    @Override
    public final Name name() {
        return name;
    }

    public boolean containsFunction(Function op) {
        final var n = functions.lookup(op.name());
        return n == op;
    }

    /// returns true if the LDT offers an operation for the given java operator and the logic
    /// subterms
    ///
    /// @param op the de.uka.ilkd.key.java.expression.Operator to translate
    /// @param subs the logic subterms of the java operator
    /// @param services the Services
    /// @param ec the ExecutionContext in which the expression is evaluated
    /// @return true if the LDT offers an operation for the given java operator and the subterms
    public abstract boolean isResponsible(Operator op, JTerm[] subs,
            Services services, ExecutionContext ec);

    /// returns true if the LDT offers an operation for the given binary java operator and the logic
    /// subterms
    ///
    /// @param op the de.uka.ilkd.key.java.expression.Operator to translate
    /// @param left the left subterm of the java operator
    /// @param right the right subterm of the java operator
    /// @param services the Services
    /// @param ec the ExecutionContext in which the expression is evaluated
    /// @return true if the LDT offers an operation for the given java operator and the subterms
    public abstract boolean isResponsible(Operator op, JTerm left,
            JTerm right, Services services, ExecutionContext ec);

    /// returns true if the LDT offers an operation for the given unary java operator and the logic
    /// subterms
    ///
    /// @param op the de.uka.ilkd.key.java.expression.Operator to translate
    /// @param sub the logic subterms of the java operator
    /// @param services the Services
    /// @param ec the ExecutionContext in which the expression is evaluated
    /// @return true if the LDT offers an operation for the given java operator and the subterm
    public abstract boolean isResponsible(Operator op, JTerm sub,
            TermServices services, ExecutionContext ec);

    /// translates a given literal to its logic counterpart
    ///
    /// @param lit the Literal to be translated
    /// @return the Term that represents the given literal in its logic form
    public abstract JTerm translateLiteral(Literal lit, Services services);

    /// returns the function symbol for the given _Java_ operator.
    ///
    /// @return the function symbol for the given operation, null if not supported in general or not
    /// supported for this particular operator.
    public abstract @Nullable Function getFunctionFor(Operator op,
            Services services, ExecutionContext ec);

    /// get the function in this LDT for an operation identified by generic operationName. If the
    /// LDT
    /// does not support this named function, it should return null.
    ///
    /// This is used to resolve overloaded symbols.
    ///
    /// For example: "+" may map to "add" for integers, and to "addFloat" for floats.
    ///
    /// @param operationName non-null operationName for a generic function
    /// @param services services to use
    /// @return reference to the respective LDT-specific function for the operation, null if not
    /// available
    public @Nullable Function getFunctionFor(String operationName, Services services) {
        // by default an LDT does not support overloaded symbols
        return null;
    }

    public abstract boolean hasLiteralFunction(Function f);

    /// Is called whenever `hasLiteralFunction()` returns true.
    public abstract Expression translateTerm(JTerm t, ExtList children, Services services);
}
