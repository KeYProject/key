package de.uka.ilkd.key.java.transformations.pipeline;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.utils.Pair;
import org.jspecify.annotations.NonNull;

import java.util.Optional;

/**
 * Replaces lambda expressions by an internal named class.
 * <p>
 * Code was donated by Carsten Czisky @ciskar
 */
public class LambdaReplacer extends JavaTransformer {

    /**
     * creates a transformer for the recoder model
     *
     * @param services the CrossReferenceServiceConfiguration to access
     *                 model information
     */
    public LambdaReplacer(@NonNull TransformationPipelineServices services) {
        super(services);
    }

    @Override
    public void apply(TypeDeclaration<?> td) {
        td.walk(LambdaExpr.class, this::rewriteLambda);
    }

    private void rewriteLambda(LambdaExpr expr) {
        @SuppressWarnings({"rawtypes", "unchecked"})
        Optional<TypeDeclaration> enclosingType = expr.findAncestor(TypeDeclaration.class);

        if (enclosingType.isEmpty()) {
            throw new IllegalStateException("LambdaExpr is not enclosed in a type declaration");
        }

        ClassOrInterfaceDeclaration decl = liftToInnerClass(expr);
        enclosingType.get().addMember(decl);

        var objectCreation = instantiate(decl);
        expr.replace(objectCreation);
    }

    private ObjectCreationExpr instantiate(ClassOrInterfaceDeclaration decl) {
        ClassOrInterfaceType type = new ClassOrInterfaceType(null, decl.getNameAsString());
        return new ObjectCreationExpr(null, type, new NodeList<>());
    }

    private ClassOrInterfaceDeclaration liftToInnerClass(LambdaExpr lambdaExpr) {
        Pair<String, MethodDeclaration> sai = findSingleAbstractInterface(lambdaExpr);
        String interfaceName = sai.a;
        MethodDeclaration method = sai.b;

        String name = services.getFreshName("__GENERATED_",
                lambdaExpr.getRange().map(r -> r.begin).orElse(null));

        ClassOrInterfaceDeclaration it =
                new ClassOrInterfaceDeclaration(new NodeList<>(), false, name);

        it.addImplementedType(interfaceName);
        it.addMember(method);

        return it;
    }

    private Pair<String, MethodDeclaration> findSingleAbstractInterface(LambdaExpr lambdaExpr) {
        ClassOrInterfaceType type = assignToType(lambdaExpr);

        if (type == null) {
            return inferDefaultAbstractInterface(lambdaExpr);
        } else {
            return new Pair<>(type.getNameAsString(), new MethodDeclaration());
        }
    }

    private Pair<String, MethodDeclaration> inferDefaultAbstractInterface(LambdaExpr lambdaExpr) {
        String interfaze;
        MethodDeclaration md = new MethodDeclaration();

        Node body = lambdaExpr.getBody();
        String returnType = null;

        if (body instanceof BlockStmt block) {
            Statement last = block.getStatements().isEmpty()
                    ? null
                    : block.getStatements().getLast();

            if (last != null && last.isReturnStmt()) {
                returnType = last.asReturnStmt()
                        .getExpression()
                        .map(e -> e.calculateResolvedType().toString())
                        .orElse(null);
            }
        }

        if (body instanceof ExpressionStmt es) {
            returnType = es.getExpression().calculateResolvedType().toString();
        }

        int paramCount = lambdaExpr.getParameters().size();

        switch (paramCount) {
            case 0:
                if (returnType == null) {
                    interfaze = "Runnable";
                    md.setName("run");
                } else {
                    interfaze = "java.util.function.Supplier<" + returnType + ">";
                    md.setName("accept");
                }
                break;

            case 1:
                String firstParam = lambdaExpr.getParameter(0).getTypeAsString();
                if (returnType == null) {
                    interfaze = "java.util.function.Consumer<" + firstParam + ">";
                    md.setName("get");
                } else {
                    interfaze = "java.util.function.Function<" + firstParam + ", " + returnType + ">";
                    md.setName("invoke");
                }
                break;

            case 2:
                String p1 = lambdaExpr.getParameter(0).getTypeAsString();
                String p2 = lambdaExpr.getParameter(1).getTypeAsString();
                if (returnType == null) {
                    interfaze = "java.util.function.BiConsumer<" + p1 + "," + p2 + ">";
                    md.setName("get");
                } else {
                    interfaze = "java.util.function.BiFunction<" + p1 + ", " + p2 + ", " + returnType + ">";
                    md.setName("invoke");
                }
                break;

            default:
                throw new IllegalStateException("ASM could not be inferred");
        }

        lambdaExpr.getParameters().forEach(p -> md.addParameter(p.clone()));

        return new Pair<>(interfaze, md);
    }

    private ClassOrInterfaceType assignToType(LambdaExpr lambdaExpr) {
        var type = lambdaExpr.calculateResolvedType();
        System.out.println("TEST: " + type);
        return null; // TODO
    }
}
