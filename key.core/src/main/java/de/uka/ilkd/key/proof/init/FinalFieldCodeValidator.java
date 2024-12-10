package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.ClassType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.Assignment;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import org.key_project.logic.SyntaxElement;
import org.key_project.util.collection.IdentityHashSet;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.Set;

/**
 * Validates the code of a constructor to ensure that final fields are not read before they are initialized.
 *
 * Currently rather strict:
 * - Called methods must not receive 'this' as an explicit parameter
 * - 'this' must not be assigned to any field or variable
 * - final fields must not be read.
 * - Methods called on 'this' must be effectively final (not overridable)
 * - Methods called on 'this' must not read any final fields as well.
 *
 * Potential for relaxaions:
 * - Final fields may be read after initialization (locally and in called methods)
 * This requires a lot more bookkeeping, though.
 * - Effective finalness can be relaxed: If every constructor is subject to this treatment,
 * corresponding expansion of the methods would reveal any illegal reads. ... if the super(...)
 * calls are expanded for analysis.
 *
 * If this is a secondary constructor (referring to another constructor via this()), there are no restrictions.
 */
class FinalFieldCodeValidator {
    private final InitConfig initConfig;
    private final Set<IProgramMethod> validatedMethods = new IdentityHashSet<>();
    private final Deque<IProgramMethod> methodStack = new ArrayDeque<>();
    private KeYJavaType enclosingClass;

    public FinalFieldCodeValidator(InitConfig initConfig) {
        this.initConfig = initConfig;
    }

    public static void validateFinalFields(ProgramMethod constructor, InitConfig initConfig) {
        var validator = new FinalFieldCodeValidator(initConfig);
        validator.enclosingClass = constructor.getContainerType();
        if(isSecondaryConstructor(constructor)) {
            // secondary constructors are fine!
            return;
        }
        validator.validate(constructor);
    }

    private static boolean isSecondaryConstructor(IProgramMethod constructor) {
        StatementBlock body = constructor.getBody();
        if(body == null) {
            return false;
        }

        if(body.getStatementCount() == 0) {
            return false;
        }

        var firstStatement = body.getStatementAt(0);
        return firstStatement instanceof ThisConstructorReference;
    }

    private void validate(IProgramMethod method) {
        if(validatedMethods.contains(method)) {
            return;
        }

        methodStack.push(method);

        StatementBlock body = method.getBody();
        if(body == null) {
            throw new FinalViolationException("Method " + method.getFullName() + " has no body.");
        }

       validateProgramElement(body);

        var popped = methodStack.pop();
        assert popped == method;
        validatedMethods.add(method);
    }

    private void validateProgramElement(SyntaxElement element) {
        if(element instanceof MethodReference methodReference) {
            validateMethodReference(methodReference);
        } else if (element instanceof ConstructorReference constructorReference) {
            validateConstructorReference(constructorReference);
        } else if(element instanceof FieldReference fieldReference) {
            validateFieldReference(fieldReference);
        } else if(element instanceof Assignment assignment) {
            validateAssignment(assignment);
        }
        // Case: "string" + this .... not allowed!
        // Case: Model method calls are as problematic as the rest ...

        for(int i = 0; i < element.getChildCount(); i++) {
            validateProgramElement(element.getChild(i));
        }
    }

    private void validateConstructorReference(ConstructorReference methodReference) {
        // TODO We have to make sure that on non-static subclass is instantiated here
        var hasThisArgument = methodReference.getArguments().stream().anyMatch(ThisReference.class::isInstance);

        if(hasThisArgument) {
            throw new FinalViolationException("Method call " + methodReference + " leaks 'this' to called method.", methodReference);
        }
    }

    private void validateMethodReference(MethodReference methodReference) {
        ReferencePrefix referencePrefix = methodReference.getReferencePrefix();
        var calledOnThis = referencePrefix == null || referencePrefix instanceof ThisReference;
        var hasThisArgument = methodReference.getArguments().stream().anyMatch(ThisReference.class::isInstance);

        if(hasThisArgument) {
            throw new FinalViolationException("Method call " + methodReference + " leaks 'this' to called method.", methodReference);
        }

        if(calledOnThis) {
            IProgramMethod method = findMethod(methodReference);
            if(method.isStatic() || method.isConstructor()) {
                // local static methods are acutally fine ...
                // constructor calls are also fine
                //    TODO (well ... what about inner classes?)
                return;
            }
            if(!method.isFinal() && !method.isPrivate() && !((ClassType)enclosingClass.getJavaType()).isFinal()) {
                throw new FinalViolationException("Method called on 'this' that is not effectively final.", methodReference);
            }
            validate(method);
        }
    }

    private IProgramMethod findMethod(MethodReference methodReference) {
        // return the program method for the method reference
        // YOu can use enclosingClass to get the class in which the method is defined
        // The method is guaranteed to be defined in the enclosing class not in a superclass.
        // One can also peek the method stack if needed ...
        ExecutionContext ec = new ExecutionContext(new TypeRef(enclosingClass), methodStack.peek(), methodReference.getReferencePrefix());
        return         methodReference.method(initConfig.getServices(), methodReference.determineStaticPrefixType(initConfig.getServices(), ec), ec);
    }

    private void validateAssignment(Assignment assignment) {
        SyntaxElement value = assignment.getChild(1);
        if (value instanceof ThisReference) {
            throw new FinalViolationException("'this' is leaked to a field or variable.", assignment);
        }
    }

    private void validateFieldReference(FieldReference fieldReference) {
        ReferencePrefix prefix = fieldReference.getReferencePrefix();
        ProgramVariable field = fieldReference.getProgramVariable();
        if(field.isFinal() && prefix instanceof ThisReference) {
            throw new FinalViolationException("Final field " + field + " is read.", fieldReference);
        }
    }

    static class FinalViolationException extends RuntimeException {

        private final Position position;

        public FinalViolationException(String message) {
            this(message, null);
        }

        public FinalViolationException(String message, SyntaxElement syntaxElement) {
            super(message);
            if (syntaxElement instanceof SourceElement sourceElement) {
                this.position = sourceElement.getStartPosition();
            } else {
                this.position = null;
            }
        }

        public Position getPosition() {
            return position;
        }
    }
}


