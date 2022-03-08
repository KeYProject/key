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

package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

import javax.annotation.Nonnull;
import java.util.List;


/**
 * A shortcut-statement for a method body, i.e. no dynamic dispatching
 * any longer.<p />
 * Please take care:
 * only the method name plus the class in which class the method
 * is implemented is part of the syntax representation of such a
 * statement, but not the methods complete syntax. If there are
 * two methods with an equal name, but different signature (i.e.
 * parameter types), the pure syntax is ambigious. In fact the concrete body
 * this method body statement represents depends on the static type of
 * its arguments. <p />
 * Therefore: Transformation of a method body statement <em>MUST</em> keep
 * the static type of the arguments <em>unchanged</em>.
 * <p/>
 */
public class MethodBodyStatement extends JavaNonTerminalProgramElement
        implements Statement, NonTerminalProgramElement {


    /**
     * the variable the result of the method execution is assigned to
     * if the method is declared void or the result not assigned to a
     * variable or field, this value is null.
     */
    private final IProgramVariable resultVar;

    /**
     * This type reference determines the class where the represented method
     * has to be implemented.
     */
    private final TypeReference bodySource;

    /**
     * the reference describing the method signature
     */
    @Nonnull
    private final MethodReference methodReference;

    /**
     * cache resolved method
     */
    private IProgramMethod method;

    public MethodBodyStatement(PositionInfo pi, List<Comment> comments, IProgramVariable resultVar,
                               TypeReference bodySource, MethodReference methodReference, IProgramMethod method) {
        super(pi, comments);
        this.resultVar = resultVar;
        this.bodySource = bodySource;
        this.methodReference = methodReference;
        this.method = method;
    }

    /**
     * Construct a method body shortcut
     *
     * @param bodySource      exact class where the body is declared
     * @param resultVar       the IProgramVariable to which the method's return value is assigned
     * @param methodReference the MethodReference encapsulating the method's signature
     */
    public MethodBodyStatement(TypeReference bodySource,
                               IProgramVariable resultVar,
                               MethodReference methodReference) {
        this(null, null, resultVar, bodySource, methodReference, null);
        assert methodReference != null : "Missing methodreference";
        assert methodReference.getReferencePrefix() != null :
                "Method reference of a method body statement needs an " +
                        "explicit reference prefix.";
        checkOnlyProgramVarsAsArguments(methodReference.getArguments());
    }

    public MethodBodyStatement(ExtList list) {
        super(list);
        this.bodySource = list.get(TypeReference.class);
        this.resultVar = list.get(IProgramVariable.class);

        this.methodReference = list.get(MethodReference.class);

        assert methodReference != null : "Missing methodreference";
        assert methodReference.getReferencePrefix() != null :
                "Method reference of a method body statement needs an " +
                        "explicit reference prefix.";
        checkOnlyProgramVarsAsArguments(methodReference.getArguments());
    }

    public MethodBodyStatement(IProgramMethod method, ReferencePrefix newContext,
                               IProgramVariable res, ImmutableArray<Expression> args) {
        this(method, newContext, res, args, null);
    }

    public MethodBodyStatement(IProgramMethod method, ReferencePrefix newContext, IProgramVariable res,
                               ImmutableArray<Expression> args, ProgramElement scope) {
        super((PositionInfo) null, null);
        this.method = method;
        this.bodySource = new TypeRef(method.getContainerType());
        this.resultVar = res;

        if (newContext == null) {
            if (method.isStatic()) {
                newContext = bodySource;
            } else {
                throw new IllegalArgumentException("The invocation target of a method body" +
                        "statement must be non null");
            }
        }

        checkOnlyProgramVarsAsArguments(args);
        this.methodReference = new MethodReference(args,
                method.getProgramElementName(),
                newContext);
    }


    private void checkOnlyProgramVarsAsArguments(ImmutableArray<? extends Expression> arguments) {
        for (int i = 0, sz = arguments.size(); i < sz; i++) {
            final Expression argument = arguments.get(i);
            if (!((argument instanceof LocationVariable && !((LocationVariable) argument).isMember()) ||
                    argument instanceof SchemaVariable)) {
                throw new IllegalArgumentException("Only local variables or schemavariables " +
                        "allowed as arguments of a method body statement.");
            }
        }
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
        return method.getBody();
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */
    public int getChildCount() {
        int i = 0;
        if (bodySource != null) i++;
        if (resultVar != null) i++;
        if (methodReference != null) i++;
        return i;
    }

    public ReferencePrefix getDesignatedContext() {
        return methodReference.getReferencePrefix();
    }

    public ImmutableArray<? extends Expression> getArguments() {
        return methodReference.getArguments();
    }

    /**
     * Returns the child at the specified index in this node's "virtual"
     * child array.
     *
     * @param index an index into this node's "virtual" child array
     * @return the program element at the given position
     * @throws ArrayIndexOutOfBoundsException if <tt>index</tt> is out
     *                                        of bounds
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
        return method.isStatic();
    }


    /**
     * calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnMethodBodyStatement(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printMethodBodyStatement(this);
    }

    public IProgramVariable getResultVariable() {
        return resultVar;
    }

    public KeYJavaType getBodySource() {
        return bodySource.getKeYJavaType();
    }

    public TypeReference getBodySourceAsTypeReference() {
        return bodySource;
    }


    public IProgramMethod getProgramMethod(Services services) {
        if (method == null) {
            resolveMethod(services);
        }
        return method;
    }

    private void resolveMethod(Services services) {
        method = services.getJavaInfo().
                getProgramMethod(getBodySource(),
                        methodReference.getName(),
                        services.getJavaInfo().
                                createSignature(methodReference.getArguments()),
                        getBodySource());
    }

    public String reuseSignature(Services services, ExecutionContext ec) {
        return super.reuseSignature(services, ec) + "(" + getBodySource().getName() + ")";
    }


    public MethodReference getMethodReference() {
        return methodReference;
    }

}