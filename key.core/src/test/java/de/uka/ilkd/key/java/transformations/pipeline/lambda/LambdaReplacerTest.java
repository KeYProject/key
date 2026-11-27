/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.transformations.pipeline.lambda;

import java.io.IOException;
import java.io.InputStream;
import java.io.StringReader;
import java.nio.charset.StandardCharsets;
import java.util.Collections;
import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.loader.JavaParserFactory;
import de.uka.ilkd.key.java.transformations.pipeline.TransformationPipelineServices;
import de.uka.ilkd.key.nparser.NamespaceBuilder;
import de.uka.ilkd.key.proof.init.JavaProfile;

import com.github.javaparser.ParseResult;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.expr.MethodReferenceExpr;
import com.github.javaparser.ast.expr.ThisExpr;
import com.github.javaparser.ast.stmt.LocalClassDeclarationStmt;
import org.junit.jupiter.api.Test;

import static com.google.common.truth.Truth.assertThat;

/**
 * Unit tests for the standalone {@link LambdaReplacer} desugaring step, driven by the fixtures in
 * {@code src/test/resources/de/uka/ilkd/key/java/transformations/pipeline/lambda/}:
 * <ul>
 * <li>{@code Test.java} — two nested lambdas capturing a field of the enclosing class,</li>
 * <li>{@code TestGeneric.java} — lambdas whose target type is a generic functional interface
 * (the type parameter is reified to the used type argument on the generated class),</li>
 * <li>{@code TestPredicateInline.java} — lambdas inside {@code default}/{@code static} methods of
 * a functional interface declared inline (including {@code this}/{@code super} escaping to the
 * enclosing interface).</li>
 * </ul>
 * <p>
 * The whole {@code pipelineTests/lambda} snapshot tests additionally cover the subsequent pipeline
 * steps (local-class hoisting, JML contract conversion of {@link LambdaContractSpec}).
 *
 * @author weigl
 */
class LambdaReplacerTest {

    private static final String FIXTURES = "/de/uka/ilkd/key/java/transformations/pipeline/lambda/";

    private static CompilationUnit transform(String fileName) throws IOException {
        try (InputStream in = LambdaReplacerTest.class.getResourceAsStream(FIXTURES + fileName)) {
            String src = new String(in.readAllBytes(), StandardCharsets.UTF_8);
            Services services = new Services(JavaProfile.getDefaultProfile());
            // Register the primitive sorts the boot-stub conversion needs, then activate the
            // JavaRedux boot stubs so that the JDK types referenced by the fixtures
            // (java.util.Objects, java.util.function.Predicate, Integer and the
            // @java.lang.FunctionalInterface marker) resolve through the factory's type solver.
            NamespaceBuilder nb = new NamespaceBuilder(services.getNamespaces());
            nb.addSort("boolean").addSort("int").addSort("Seq").addSort("LocSet").addSort("double")
                    .addSort("float");
            var js = services.activateJava(null, Collections.emptyList(), null);
            js.parseSpecialClasses();
            JavaParserFactory factory = js.getProgramFactory();
            ParseResult<CompilationUnit> result =
                factory.parseCompilationUnit(new StringReader(src));
            assertThat(result.isSuccessful())
                    .isTrue();
            CompilationUnit cu = result.getResult().orElseThrow();
            TransformationPipelineServices ps = new TransformationPipelineServices(factory,
                new TransformationPipelineServices.TransformerCache(List.of(cu)));
            new LambdaReplacer(ps).apply(cu);
            return cu;
        }
    }

    private static List<ClassOrInterfaceDeclaration> generatedClasses(CompilationUnit cu) {
        return cu.findAll(LocalClassDeclarationStmt.class).stream()
                .map(LocalClassDeclarationStmt::getClassDeclaration)
                .toList();
    }

    private static ClassOrInterfaceDeclaration generatedClass(CompilationUnit cu, String name) {
        return generatedClasses(cu).stream()
                .filter(c -> c.getNameAsString().equals(name))
                .findFirst().orElseThrow();
    }

    private static MethodDeclaration samOf(ClassOrInterfaceDeclaration local) {
        List<MethodDeclaration> methods =
            local.getMembers().stream().filter(MethodDeclaration.class::isInstance)
                    .map(MethodDeclaration.class::cast)
                    .toList();
        assertThat(methods).hasSize(1);
        return methods.get(0);
    }

    private static void assertNoLambdasLeft(CompilationUnit cu) {
        assertThat(cu.findAll(LambdaExpr.class)).isEmpty();
        assertThat(cu.findAll(MethodReferenceExpr.class)).isEmpty();
    }

    @Test
    void nestedLambdasDesugarToTwoLocalClasses() throws IOException {
        CompilationUnit cu = transform("Test.java");
        assertNoLambdasLeft(cu);
        assertThat(generatedClasses(cu)).hasSize(2);

        ClassOrInterfaceDeclaration inner = generatedClass(cu, "MyFunctionalInterface__1");
        assertThat(inner.getImplementedTypes().toString()).isEqualTo("[A.MyFunctionalInterface]");
        MethodDeclaration innerSam = samOf(inner);
        assertThat(innerSam.getType().asString()).isEqualTo("int");
        assertThat(innerSam.getNameAsString()).isEqualTo("apply");
        assertThat(innerSam.getParameters()).hasSize(1);
        assertThat(innerSam.getParameter(0).getNameAsString()).isEqualTo("x");

        ClassOrInterfaceDeclaration outer = generatedClass(cu, "MyFunctionalInterface__2");
        assertThat(outer.getImplementedTypes().toString()).isEqualTo("[A.MyFunctionalInterface]");
        MethodDeclaration outerSam = samOf(outer);
        assertThat(outerSam.getType().asString()).isEqualTo("int");
        assertThat(outerSam.getParameter(0).getNameAsString()).isEqualTo("a");
        // The outer lambda body instantiates the desugared inner lambda.
        assertThat(outerSam.findAll(com.github.javaparser.ast.expr.ObjectCreationExpr.class)
                .stream()
                .anyMatch(ce -> ce.getTypeAsString().equals("MyFunctionalInterface__1")))
                .isTrue();
    }

    @Test
    void genericFunctionalInterfaceTypeArgumentsAreReified() throws IOException {
        CompilationUnit cu = transform("TestGeneric.java");
        assertNoLambdasLeft(cu);
        assertThat(generatedClasses(cu)).hasSize(2);

        ClassOrInterfaceDeclaration inner = generatedClass(cu, "MyFunctionalInterface__1");
        assertThat(inner.getImplementedTypes().toString())
                .isEqualTo("[A.MyFunctionalInterface<java.lang.Integer>]");
        MethodDeclaration innerSam = samOf(inner);
        assertThat(innerSam.getType().asString()).isEqualTo("boolean");
        assertThat(innerSam.getParameter(0).getType().asString()).isEqualTo("java.lang.Integer");

        ClassOrInterfaceDeclaration outer = generatedClass(cu, "MyFunctionalInterface__2");
        assertThat(outer.getImplementedTypes().toString())
                .isEqualTo("[A.MyFunctionalInterface<java.lang.Integer>]");
        assertThat(samOf(outer).getParameter(0).getType().asString())
                .isEqualTo("java.lang.Integer");
    }

    @Test
    void lambdasInDefaultAndStaticMethodsDesugarAndEscapeThis() throws IOException {
        CompilationUnit cu = transform("TestPredicateInline.java");
        assertNoLambdasLeft(cu);
        assertThat(generatedClasses(cu)).hasSize(6);

        // Target typed by Predicate<Integer> keeps the type argument on the generated class.
        ClassOrInterfaceDeclaration direct = generatedClass(cu, "Predicate__1");
        assertThat(direct.getImplementedTypes().toString())
                .isEqualTo("[A.Predicate<java.lang.Integer>]");
        assertThat(samOf(direct).getParameter(0).getType().asString())
                .isEqualTo("java.lang.Integer");

        // The lambdas inside the default methods live in raw (type-erased) target type context.
        for (String name : List.of("Predicate__2", "Predicate__3", "Predicate__4",
            "Predicate__5", "Predicate__6")) {
            ClassOrInterfaceDeclaration local = generatedClass(cu, name);
            assertThat(local.getImplementedTypes().toString()).isEqualTo("[A.Predicate]");
            MethodDeclaration sam = samOf(local);
            assertThat(sam.getType().asString()).isEqualTo("boolean");
            assertThat(sam.getNameAsString()).isEqualTo("test");
            assertThat(sam.getParameter(0).getType().asString()).isEqualTo("java.lang.Object");
        }

        // `this` inside the desugared default/static method bodies refers to the enclosing
        // interface: escaped to Predicate.this.
        assertThat(samOf(generatedClass(cu, "Predicate__2")).findAll(ThisExpr.class)
                .stream()
                .anyMatch(te -> te.getTypeName().isPresent()
                        && te.getTypeName().get().asString().equals("Predicate")))
                .isTrue();
    }
}
