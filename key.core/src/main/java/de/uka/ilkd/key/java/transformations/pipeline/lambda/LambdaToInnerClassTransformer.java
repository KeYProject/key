package de.uka.ilkd.key.java.transformations.pipeline.lambda;

import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.*;
import com.github.javaparser.ast.visitor.*;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;

import java.util.*;

/**
 * Transforms lambda expressions into named inner classes that implement the
 * appropriate Single Abstract Method (SAM) interface.
 */
public class LambdaToInnerClassTransformer extends VoidVisitorAdapter<Void> {

    private final String classPrefix;
    private int counter = 0;
    private final List<TypeDeclaration<?>> generatedInnerClasses = new ArrayList<>();

    /**
     * Constructs a LambdaToInnerClassTransformer.
     *
     * @param classPrefix the prefix for generated class names
     */
    public LambdaToInnerClassTransformer(String classPrefix) {
        this.classPrefix = classPrefix;
    }

    /**
     * Gets the list of generated inner classes.
     *
     * @return list of generated type declarations
     */
    public List<TypeDeclaration<?>> getGeneratedInnerClasses() {
        return generatedInnerClasses;
    }

    @Override
    public void visit(LambdaExpr lambdaExpr, Void arg) {
        super.visit(lambdaExpr, arg);

        // Determine the parent node context
        Node parent = lambdaExpr.getParentNode().orElse(null);
        if (parent == null) {
            return;
        }

        // Generate a unique name for the inner class
        String className = classPrefix + "_" + (counter++);

        // Create the inner class replacement
        Expression innerClassInstance = createInnerClassForLambda(lambdaExpr, className);

        // Replace the lambda with the inner class instantiation
        lambdaExpr.replace(innerClassInstance);
    }

    /**
     * Creates an inner class definition and returns an expression to instantiate it.
     *
     * @param lambdaExpr the lambda expression to convert
     * @param className the name for the generated inner class
     * @return an expression that instantiates the generated inner class
     */
    private Expression createInnerClassForLambda(LambdaExpr lambdaExpr, String className) {
        // Resolve the lambda's functional interface type
        ResolvedType resolvedType = lambdaExpr.calculateResolvedType();
        ResolvedReferenceTypeDeclaration functionalInterface = resolvedType.asReferenceType().getTypeDeclaration();

        // Find the single abstract method (SAM)
        ResolvedMethodDeclaration sam = findSam(functionalInterface);

        // Extract captured variables (free variables)
        List<CapturedVariable> capturedVariables = findCapturedVariables(lambdaExpr);

        // Create the inner class declaration
        ClassOrInterfaceDeclaration innerClass = new ClassOrInterfaceDeclaration(
            new NodeList<>(Modifier.publicModifier(), Modifier.staticModifier(), Modifier.finalModifier()),
            false,
            className
        );

        // Add fields for captured variables
        for (CapturedVariable captured : capturedVariables) {
            FieldDeclaration field = new FieldDeclaration(
                new NodeList<>(Modifier.privateModifier(), Modifier.finalModifier()),
                captured.getType(),
                captured.getName()
            );
            innerClass.addMember(field);
        }

        // Add constructor that accepts captured variables
        ConstructorDeclaration constructor = new ConstructorDeclaration(
            new NodeList<>(Modifier.publicModifier()),
            className
        );

        // Add constructor parameters and assignments
        for (CapturedVariable captured : capturedVariables) {
            Parameter param = new Parameter(captured.getType(), captured.getName());
            constructor.addParameter(param);

            // Create assignment: this.fieldName = fieldName
            AssignExpr assignExpr = new AssignExpr(
                new FieldAccessExpr(new ThisExpr(), captured.getName()),
                new NameExpr(captured.getName()),
                AssignExpr.Operator.ASSIGN
            );
            constructor.getBody().get().addStatement(new ExpressionStmt(assignExpr));
        }
        innerClass.addMember(constructor);

        // Implement the SAM method
        MethodDeclaration methodImpl = new MethodDeclaration(
            new NodeList<>(Modifier.publicModifier()),
            sam.getReturnType(),
            sam.getName()
        );

        // Add parameters matching SAM signature
        for (int i = 0; i < sam.getNumberOfParams(); i++) {
            var param = sam.getParam(i);
            methodImpl.addParameter(param.getType(), param.getName());
        }

        // Set the method body based on lambda body
        setMethodBody(methodImpl, lambdaExpr, sam);

        innerClass.addMember(methodImpl);

        // Store the generated class
        generatedInnerClasses.add(innerClass);

        // Create the instantiation expression
        ObjectCreationExpr creationExpr = new ObjectCreationExpr();
        creationExpr.setType(className);

        // Add arguments for captured variables
        for (CapturedVariable captured : capturedVariables) {
            creationExpr.addArgument(new NameExpr(captured.getName()));
        }

        return creationExpr;
    }

    /**
     * Finds the Single Abstract Method in a functional interface.
     *
     * @param functionalInterface the functional interface declaration
     * @return the single abstract method
     */
    private ResolvedMethodDeclaration findSam(ResolvedReferenceTypeDeclaration functionalInterface) {
        List<ResolvedMethodDeclaration> abstractMethods = new ArrayList<>();

        for (ResolvedMethodDeclaration method : functionalInterface.getDeclaredMethods()) {
            if (method.isAbstract() && !method.isDefaultMethod()) {
                abstractMethods.add(method);
            }
        }

        if (abstractMethods.size() != 1) {
            throw new IllegalStateException(
                "Expected exactly one abstract method in functional interface, found: " + abstractMethods.size()
            );
        }

        return abstractMethods.get(0);
    }

    /**
     * Finds all captured (free) variables in a lambda expression.
     *
     * @param lambdaExpr the lambda expression
     * @return list of captured variables
     */
    private List<CapturedVariable> findCapturedVariables(LambdaExpr lambdaExpr) {
        CapturedVariableCollector collector = new CapturedVariableCollector();
        lambdaExpr.getBody().accept(collector, null);

        // Remove lambda parameters from captured variables
        Set<String> paramNames = new HashSet<>();
        for (Parameter param : lambdaExpr.getParameters()) {
            paramNames.add(param.getNameAsString());
        }

        List<CapturedVariable> captured = new ArrayList<>();
        for (CapturedVariable var : collector.getCapturedVariables()) {
            if (!paramNames.contains(var.getName())) {
                captured.add(var);
            }
        }

        return captured;
    }

    /**
     * Sets the method body based on the lambda body.
     *
     * @param methodDecl the method declaration to populate
     * @param lambdaExpr the source lambda expression
     * @param sam the single abstract method
     */
    private void setMethodBody(MethodDeclaration methodDecl, LambdaExpr lambdaExpr, ResolvedMethodDeclaration sam) {
        var lambdaBody = lambdaExpr.getBody();

        // Check if SAM returns void
        if (sam.getReturnType().isVoid()) {
            methodDecl.setBody(new BlockStmt(new NodeList<>(new ExpressionStmt(lambdaBody))));
        } else {
            methodDecl.setBody(new BlockStmt(new NodeList<>(new ReturnStmt(lambdaBody.asExpressionStmt().expression()))));
        }
    }

    /**
     * Represents a captured variable with its type and name.
     */
    private static class CapturedVariable {
        private final Type type;
        private final String name;

        CapturedVariable(Type type, String name) {
            this.type = type;
            this.name = name;
        }

        Type getType() {
            return type;
        }

        String getName() {
            return name;
        }
    }

    /**
     * Visitor that collects captured variables from a lambda body.
     */
    private static class CapturedVariableCollector extends VoidVisitorAdapter<Void> {
        private final List<CapturedVariable> capturedVariables = new ArrayList<>();
        private final Set<String> declaredInScope = new HashSet<>();

        @Override
        public void visit(NameExpr nameExpr, Void arg) {
            super.visit(nameExpr, arg);

            // Try to resolve the name and check if it's a captured variable
            try {
                var resolved = nameExpr.resolve();
                String name = nameExpr.getNameAsString();

                // Skip if already declared in local scope
                if (declaredInScope.contains(name)) {
                    return;
                }

                // Add as captured variable
                Type type = parseType(resolved.describeType());
                capturedVariables.add(new CapturedVariable(type, name));
            } catch (Exception e) {
                // Resolution failed, skip this name
            }
        }

        @Override
        public void visit(Parameter parameter, Void arg) {
            super.visit(parameter, arg);
            declaredInScope.add(parameter.getNameAsString());
        }

        @Override
        public void visit(VariableDeclarationExpr varDecl, Void arg) {
            super.visit(varDecl, arg);
            for (VariableDeclarator vd : varDecl.getVariables()) {
                declaredInScope.add(vd.getNameAsString());
            }
        }

        List<CapturedVariable> getCapturedVariables() {
            // Deduplicate by name
            Map<String, CapturedVariable> unique = new LinkedHashMap<>();
            for (CapturedVariable cv : capturedVariables) {
                unique.putIfAbsent(cv.getName(), cv);
            }
            return new ArrayList<>(unique.values());
        }

        /**
         * Parses a type description string into a Type object.
         */
        private Type parseType(String typeDescription) {
            // Handle common primitive types and simple references
            return switch (typeDescription) {
                case "int" -> PrimitiveType.intType();
                case "long" -> PrimitiveType.longType();
                case "double" -> PrimitiveType.doubleType();
                case "float" -> PrimitiveType.floatType();
                case "boolean" -> PrimitiveType.booleanType();
                case "byte" -> PrimitiveType.byteType();
                case "short" -> PrimitiveType.shortType();
                case "char" -> PrimitiveType.charType();
                case "void" -> new VoidType();
                default -> new ClassOrInterfaceType(null, typeDescription);
            };
        }
    }
}