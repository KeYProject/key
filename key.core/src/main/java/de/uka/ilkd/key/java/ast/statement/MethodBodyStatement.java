/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.ast.statement;

import java.util.List;
import java.util.Objects;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.ast.*;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.reference.*;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;

import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * A shortcut-statement for a method body, i.e. no dynamic dispatching any longer.
 * <p />
 * Please take care: only the method name plus the class in which class the method is implemented is
 * part of the syntax representation of such a statement, but not the methods complete syntax. If
 * there are two methods with an equal name, but different signature (i.e. parameter types), the
 * pure syntax is ambigious. In fact the concrete body this method body statement represents depends
 * on the static type of its arguments.
 * <p />
 * Therefore: Transformation of a method body statement <em>MUST</em> keep the static type of the
 * arguments <em>unchanged</em>.
 * <p />
 *
 *
 */
@NullMarked
public class MethodBodyStatement extends JavaNonTerminalProgramElement
        implements Statement {

    /**
     * the variable the result of the method execution is assigned to if the method is declared void
     * or the result not assigned to a variable or field, this value is null.
     */
    private final @Nullable IProgramVariable resultVar;

    /**
     * This type reference determines the class where the represented method has to be implemented.
     */
    private final TypeReference bodySource;

    /**
     * the reference describing the method signature
     */
    private final MethodReference methodReference;

    /** cache resolved method */
    private @Nullable IProgramMethod method;

    /**
     * indicates whether this stands for the specification of a method rather than the concrete body
     */
    private final boolean useSpecification;

    /**
     * Construct a method body shortcut
     *
     * @param bodySource
     *        exact class where the body is declared
     * @param resultVar
     *        the IProgramVariable to which the method's return value is assigned
     * @param methodReference
     *        the MethodReference encapsulating the method's signature
     */
    public MethodBodyStatement(TypeReference bodySource, IProgramVariable resultVar,
            MethodReference methodReference) {
        this.bodySource = bodySource;
        this.resultVar = resultVar;
        this.methodReference = methodReference;
        this.useSpecification = false;

        assert methodReference != null : "Missing methodreference";
        assert methodReference.getReferencePrefix() != null
                : "Method reference of a method body statement needs an "
                    + "explicit reference prefix.";
        checkOnlyProgramVarsAsArguments(methodReference.getArguments());
    }

    public MethodBodyStatement(ExtList list) {
        this.bodySource = Objects.requireNonNull(list.get(TypeReference.class),
            "method body statement needs a body source type reference");
        this.resultVar = list.get(IProgramVariable.class);

        this.methodReference = Objects.requireNonNull(list.get(MethodReference.class),
            "method body statement needs a method reference");

        assert methodReference != null : "Missing methodreference";
        assert methodReference.getReferencePrefix() != null
                : "Method reference of a method body statement needs an "
                    + "explicit reference prefix.";
        checkOnlyProgramVarsAsArguments(methodReference.getArguments());
        this.useSpecification = false;
    }

    public MethodBodyStatement(IProgramMethod method, ReferencePrefix newContext,
            IProgramVariable res, ImmutableArray<Expression> args, boolean useSpecification) {
        this(method, newContext, res, args, useSpecification, null);
    }

    public MethodBodyStatement(IProgramMethod method, ReferencePrefix newContext,
            IProgramVariable res, ImmutableArray<Expression> args, boolean useSpecification,
            @Nullable ProgramElement scope) {
        this.method = method;
        this.bodySource = new TypeRef(Objects.requireNonNull(method.getContainerType(),
            "a program method must have a container type"));
        this.resultVar = res;
        this.useSpecification = useSpecification;

        if (newContext == null) {
            if (method.isStatic()) {
                newContext = bodySource;
            } else {
                throw new IllegalArgumentException(
                    "The invocation target of a method body" + "statement must be non null");
            }
        }

        checkOnlyProgramVarsAsArguments(args);
        this.methodReference =
            new MethodReference(args, method.getProgramElementName(), newContext);
    }

    public MethodBodyStatement(PositionInfo pi, List<Comment> c, IProgramVariable resultVar,
            TypeReference bodySource,
            MethodReference methodReference) {
        super(pi, c);
        this.resultVar = resultVar;
        this.bodySource = bodySource;
        this.methodReference = methodReference;
        // TODO weigl default value of this parameter on main?
        this.useSpecification = true;
    }


    private void checkOnlyProgramVarsAsArguments(ImmutableArray<? extends Expression> arguments) {
        for (int i = 0, sz = arguments.size(); i < sz; i++) {
            final Expression argument = arguments.get(i);
            if (!((argument instanceof LocationVariable locVar
                    && !locVar.isMember())
                    || argument instanceof SchemaVariable)) {
                throw new IllegalArgumentException("Only local variables or schemavariables "
                    + "allowed as arguments of a method body statement.");
            }
        }
    }

    public MethodBodyStatement(IProgramMethod method, ReferencePrefix newContext,
            IProgramVariable res, ImmutableArray<Expression> args) {
        this(method, newContext, res, args, false);
    }

    public MethodBodyStatement(IProgramMethod method, ReferencePrefix newContext,
            IProgramVariable res, ImmutableArray<Expression> args, ProgramElement scope) {
        this(method, newContext, res, args, false, scope);
    }

    /**
     * Get method body.
     *
     * @return the Statement
     */
    public Statement getBody(Services services) {
        if (method == null) {
            resolveMethod(services);
        }
        return Objects.requireNonNull(
            Objects.requireNonNull(method, "method body statement did not resolve its method")
                    .getBody(),
            "method body statement resolved a method without a body");
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */
    public int getChildCount() {
        int i = 0;
        if (bodySource != null) {
            i++;
        }
        if (resultVar != null) {
            i++;
        }
        if (methodReference != null) {
            i++;
        }
        return i;
    }

    public ReferencePrefix getDesignatedContext() {
        return methodReference.getReferencePrefix();
    }

    public ImmutableArray<? extends Expression> getArguments() {
        return methodReference.getArguments();
    }

    /**
     * Returns the child at the specified index in this node's "virtual" child array.
     *
     * @param index
     *        an index into this node's "virtual" child array
     * @return the program element at the given position
     * @exception ArrayIndexOutOfBoundsException
     *            if <tt>index</tt> is out of bounds
     */
    public ProgramElement getChildAt(int index) {
        if (bodySource != null) {
            if (index == 0) {
                return bodySource;
            }
            index--;
        }

        if (resultVar != null) {
            if (index == 0) {
                return resultVar;
            }
            index--;
        }

        if (methodReference != null) {
            if (index == 0) {
                return methodReference;
            }
        }

        throw new ArrayIndexOutOfBoundsException();
    }

    public boolean isStatic(Services services) {
        if (method == null) {
            resolveMethod(services);
        }
        return Objects.requireNonNull(method, "method body statement did not resolve its method")
                .isStatic();
    }


    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v
     *        the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnMethodBodyStatement(this);
    }

    public @Nullable IProgramVariable getResultVariable() {
        return resultVar;
    }

    public KeYJavaType getBodySource() {
        return Objects.requireNonNull(bodySource.getKeYJavaType(),
            "body source type reference must resolve to a KeYJavaType");
    }

    public TypeReference getBodySourceAsTypeReference() {
        return bodySource;
    }


    public IProgramMethod getProgramMethod(Services services) {
        if (method == null) {
            resolveMethod(services);
        }
        return Objects.requireNonNull(method, "method body statement did not resolve its method");
    }

    private void resolveMethod(Services services) {
        method = services.getJavaInfo().getProgramMethod(getBodySource(),
            Objects.requireNonNull(methodReference.getName(),
                "method body statement needs a named method reference"),
            services.getJavaInfo().createSignature(methodReference.getArguments()),
            getBodySource());
    }

    public String reuseSignature(Services services, ExecutionContext ec) {
        return super.reuseSignature(services, ec) + "(" + getBodySource().getName() + ")";
    }



    public MethodReference getMethodReference() {
        return methodReference;
    }

    public boolean replaceBySpecification() {
        return useSpecification;
    }

}
