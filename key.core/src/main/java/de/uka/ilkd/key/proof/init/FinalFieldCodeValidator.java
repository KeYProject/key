/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.init;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.Set;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.ClassType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.expression.Assignment;
import de.uka.ilkd.key.java.expression.operator.New;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.util.parsing.LocatableException;

import org.key_project.logic.SyntaxElement;
import org.key_project.util.collection.IdentityHashSet;

/**
 * Validates a constructor to ensure that the executed code does not read final fields before they
 * have been initialized. This is implemented by a rather straightforward static analysis of the
 * code.
 * <p>
 * Currently, the rather rules to be obeyed here are rather strict, but safe:
 * <ul>
 * <li>Called methods must not receive 'this' as an explicit parameter.</li>
 * <li>'this' must not be assigned to any field or variable.</li>
 * <li>'final' fields must not be read.</li>
 * <li>Methods called on 'this' must be effectively final (not overridable).</li>
 * <li>The body of methods called on 'this' must not read any final fields as well.
 * (This applies transitively.)</li>
 * </ul>
 * <p>
 * There is some potential for relaxations should the above rules turn out to be too strict
 * in practice:
 * <ul>
 * <li>Final fields may be read after their initialization (locally and also in called methods).
 * This requires a lot more bookkeeping, though.</li>
 * <li>Effective 'final'-ness can be relaxed: If every constructor of every subclass is subject
 * to this treatment, violations would still be observable by expanding methods, and any
 * illegal reads would be revealed. That would require 'super(...)' calls to be expanded
 * for analysis.</li>
 * </ul>
 * <p>
 * There are no restrictions for secondary constructors (referring to another constructor
 * via 'this(...)').
 * </p>
 *
 * @author Mattias Ulbrich
 * @since 2024-12-10
 */

class FinalFieldCodeValidator {
    private final InitConfig initConfig;
    private final KeYJavaType enclosingClass;

    /**
     * Methods that have already been validated so far.
     */
    private final Set<IProgramMethod> validatedMethods = new IdentityHashSet<>();

    /**
     * Stack of methods currently being validated. Needed to resolve method references.
     */
    private final Deque<IProgramMethod> methodStack = new ArrayDeque<>();

    private FinalFieldCodeValidator(InitConfig initConfig, KeYJavaType containerType) {
        this.initConfig = initConfig;
        this.enclosingClass = containerType;
    }

    /**
     * Validates the given constructor.
     *
     * The method does not do anything if the constructor is not problematic.
     * If the code is deemed problematic a {@link FinalViolationException} is thrown.
     *
     * @param constructor the constructor to validate
     * @param initConfig the init config to be used during validation
     * @throws FinalViolationException if the code is considered problematic wrt. final fields
     */
    public static void validateFinalFields(ProgramMethod constructor, InitConfig initConfig) {
        var validator = new FinalFieldCodeValidator(initConfig, constructor.getContainerType());
        if (isSecondaryConstructor(constructor)) {
            // secondary constructors are fine!
            return;
        }
        validator.validate(constructor);
    }

    /*
     * Secondary constructors have a 'this(...)' (ThisConstructorReference) as their first
     * statement.
     */
    private static boolean isSecondaryConstructor(IProgramMethod constructor) {
        StatementBlock body = constructor.getBody();
        if (body == null) {
            return false;
        }

        if (body.getStatementCount() == 0) {
            return false;
        }

        var firstStatement = body.getStatementAt(0);
        return firstStatement instanceof ThisConstructorReference;
    }

    /*
     * Recursively validate code and all called methods.
     *
     */
    private void validate(IProgramMethod method) {
        if (validatedMethods.contains(method)) {
            return;
        }

        methodStack.push(method);

        StatementBlock body = method.getBody();
        if (body == null) {
            throw new FinalViolationException("Method " + method.getFullName() + " has no body.");
        }

        validateProgramElement(body);

        var popped = methodStack.pop();
        assert popped == method;
        validatedMethods.add(method);
    }

    /*
     * Recursively validate code and all called methods. Makes case distinctions for different
     * program elements.
     */
    private void validateProgramElement(SyntaxElement element) {
        if (element instanceof MethodReference methodReference) {
            validateMethodReference(methodReference);
        } else if (element instanceof New _new) {
            validateNew(_new);
        } else if (element instanceof FieldReference fieldReference) {
            validateFieldReference(fieldReference);
        } else if (element instanceof Assignment assignment) {
            validateAssignment(assignment);
        } else {
            validateChildren(element);
        }
        // Case: "string" + this .... not allowed!
        // Case: Model method calls are as problematic as the rest ...

    }

    /*
     * Recursively validate all children of the given element.
     */
    private void validateChildren(SyntaxElement element) {
        for (int i = 0; i < element.getChildCount(); i++) {
            validateProgramElement(element.getChild(i));
        }
    }

    /*
     * Constructor calls must not leak 'this' to the called constructor.
     */
    private void validateNew(New _new) {

        TypeReference typeRef = _new.getTypeReference();
        Type type = typeRef.getKeYJavaType().getJavaType();
        if (type instanceof ClassDeclaration classType && classType.isInnerClass()
                && !classType.isStatic()) {
            // This also disallows things like "a.new B()" which would not like this. However,
            // KeY cannot deal with this anyway, so we can do the easy check here.
            throw new FinalViolationException(
                "Constructor call to non-static inner class " + classType.getFullName() +
                    " leaks 'this' to the constructor",
                _new);
        }

        var hasThisArgument =
            _new.getArguments().stream().anyMatch(ThisReference.class::isInstance);

        if (hasThisArgument) {
            throw new FinalViolationException(
                "Method call " + _new + " leaks 'this' to called method.", _new);
        }

        validateChildren(_new);
    }

    /*
     * Method calls must not leak 'this' to the called method (other than as receiver)
     * Method calls on 'this' must be effectively final and are recursively validated.
     */
    private void validateMethodReference(MethodReference methodReference) {
        ReferencePrefix referencePrefix = methodReference.getReferencePrefix();
        var calledOnThis = referencePrefix == null || referencePrefix instanceof ThisReference;
        var hasThisArgument =
            methodReference.getArguments().stream().anyMatch(ThisReference.class::isInstance);

        if (hasThisArgument) {
            throw new FinalViolationException(
                "Method call to " + methodReference.getName() + " leaks 'this' to called method.",
                methodReference);
        }

        if (calledOnThis) {
            IProgramMethod method = findMethod(methodReference);
            assert !method.isConstructor()
                    : "Constructor calls should have been handled by the New handler above.";
            if (method.isStatic() || method.isConstructor()) {
                // local static methods are acutally fine ...
                // constructor calls are also fine
                // TODO (well ... what about inner classes? Aren't they evil?)
                return;
            }
            if (!method.isFinal() && !method.isPrivate()
                    && !((ClassType) enclosingClass.getJavaType()).isFinal()) {
                throw new FinalViolationException(
                    "Method to " + method.getFullName() +
                        " called on 'this' that is not effectively final.",
                    methodReference);
            }
            validate(method);
        }

        validateChildren(methodReference);
    }

    private IProgramMethod findMethod(MethodReference methodReference) {
        ExecutionContext ec = new ExecutionContext(new TypeRef(enclosingClass), methodStack.peek(),
            methodReference.getReferencePrefix());
        return methodReference.method(initConfig.getServices(),
            methodReference.determineStaticPrefixType(initConfig.getServices(), ec), ec);
    }

    /*
     * Validate assignments. 'this' must not be assigned to any field or variable.
     * References to final fields are ok on the left hand side.
     */
    private void validateAssignment(Assignment assignment) {
        SyntaxElement assignee = assignment.getChild(0);
        SyntaxElement value = assignment.getChild(1);
        if (value instanceof ThisReference) {
            throw new FinalViolationException("'this' is leaked to a field or variable.",
                assignment);
        }
        if (assignee instanceof FieldReference fr) {
            // it is ok to assign to this.finalfield!
            validateProgramElement(fr.getReferencePrefix());
        } else {
            validateProgramElement(assignee);
        }
        validateProgramElement(value);
    }

    /*
     * Validate field references. Final fields must not be read. (Exception see assignment.)
     */
    private void validateFieldReference(FieldReference fieldReference) {
        ReferencePrefix prefix = fieldReference.getReferencePrefix();
        ProgramVariable field = fieldReference.getProgramVariable();
        if (field.isFinal() && prefix instanceof ThisReference) {
            throw new FinalViolationException("Final field " + field + " is read.", fieldReference);
        }
        validateChildren(fieldReference);
    }

    static class FinalViolationException extends LocatableException {

        public FinalViolationException(String message) {
            this(message, null);
        }

        public FinalViolationException(String message, SyntaxElement syntaxElement) {
            super(message, computeLocation(syntaxElement));
        }

        private static Location computeLocation(SyntaxElement syntaxElement) {
            if (syntaxElement instanceof SourceElement sourceElement) {
                PositionInfo posInfo = sourceElement.getPositionInfo();
                var uri = posInfo.getURI().orElse(null);
                var pos = posInfo.getStartPosition();
                return new Location(uri, pos);
            }
            return Location.UNDEFINED;
        }
    }
}
