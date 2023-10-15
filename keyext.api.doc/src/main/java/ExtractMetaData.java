import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.expr.MemberValuePair;
import com.github.javaparser.ast.nodeTypes.NodeWithJavadoc;
import com.github.javaparser.javadoc.JavadocBlockTag;
import com.github.javaparser.resolution.SymbolResolver;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.TypeSolverBuilder;
import com.github.javaparser.utils.SourceRoot;

import javax.annotation.Nonnull;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (14.10.23)
 */
public class ExtractMetaData {
    private static PrintWriter out;

    public static void main(String[] args) throws IOException {
        System.out.println("XXX" + Arrays.toString(args));
        ParserConfiguration config = new ParserConfiguration();
        config.setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_17_PREVIEW);
        /*config.setAttributeComments(true);
        config.setLexicalPreservationEnabled(false);
        config.setStoreTokens(false);
        config.setIgnoreAnnotationsWhenAttributingComments(true);
        config.setDoNotAssignCommentsPrecedingEmptyLines(true);*/
        //var root = Paths.get(args[0]);
        TypeSolver typeSolver = new TypeSolverBuilder()
                .withSourceCode("keyext.api/src/main/java")
                .withSourceCode("key.core/src/main/java")
                .withSourceCode("key.util/src/main/java")
                .withCurrentJRE()
                .build();
        SymbolResolver symbolResolver = new JavaSymbolSolver(typeSolver);
        config.setSymbolResolver(symbolResolver);
        var source = new SourceRoot(Paths.get("keyext.api", "src", "main", "java"), config);
        var cu = source.tryToParse();
        var jsonSegment = Comparator.comparing(ExtractMetaData::getJsonSegment);
        var segments = cu.stream().filter(ParseResult::isSuccessful)
                .filter(it -> it.getResult().get().getPrimaryType().isPresent())
                .map(it -> it.getResult().get().getPrimaryType().get())
                .filter(ExtractMetaData::hasJsonSegment)
                .sorted(jsonSegment)
                .toList();

        try (var out = new PrintWriter(new FileWriter("doc.md"))) {
            ExtractMetaData.out = out;
            printHeader(segments);
            segments.forEach(ExtractMetaData::printDocumentation);
            printFooter(segments);
        }

        // "org.keyproject.key.api.remoteapi.KeyApi";
    }

    private static void printDocumentation(TypeDeclaration<?> typeDeclaration) {
        out.format("## Group: %s%n%n", getJsonSegment(typeDeclaration));
        out.println(getJavaDoc(typeDeclaration));
        out.println("\n");

        for (MethodDeclaration method : typeDeclaration.getMethods()) {
            if (!isExported(method)) continue;

            String callName = getCallName(method, typeDeclaration);

            out.format("### %s (type: %s) %n%n", callName, type(method));

            out.println(getJavaDoc(method));

            out.println();
        }
    }

    private static String getCallName(MethodDeclaration m, TypeDeclaration<?> td) {
        var annotationExpr = m.getAnnotationByName("JsonNotification").or(
                        () -> m.getAnnotationByName("JsonRequest"))
                .orElseThrow();

        var segment = getJsonSegment(td) + "/";
        String name = "";

        if (annotationExpr.isMarkerAnnotationExpr()) {
            name = m.getNameAsString();
        } else if (annotationExpr.isSingleMemberAnnotationExpr()) {
            var sma = annotationExpr.asSingleMemberAnnotationExpr();
            name = sma.getMemberValue().asLiteralStringValueExpr().getValue();
        } else {
            var ne = annotationExpr.asNormalAnnotationExpr();
            for (MemberValuePair pair : ne.getPairs()) {
                switch (pair.getName().asString()) {
                    case "value":
                        name = pair.getValue().asLiteralStringValueExpr().getValue();
                        break;
                    case "useSegment":
                        if (!pair.getValue().asBooleanLiteralExpr().getValue()) {
                            segment = "";
                        }
                }
            }
        }
        return segment + name;
    }


    @Nonnull
    private static String getJavaDoc(NodeWithJavadoc<?> typeDeclaration) {
        if (typeDeclaration.getJavadoc().isPresent()) {
            final var javadoc = typeDeclaration.getJavadoc().get();
            return javadoc.getDescription().toText()
                    + "\n\n"
                    + javadoc.getBlockTags().stream().map(it -> "* " + it.toText())
                    .collect(Collectors.joining("\n"));
        }
        return "";
    }

    private static String type(MethodDeclaration method) {
        if (method.getAnnotationByName("JsonNotification").isPresent())
            return "notification";
        if (method.getAnnotationByName("JsonRequest").isPresent())
            return "request";
        return "";
    }

    private static boolean isExported(MethodDeclaration method) {
        return method.getAnnotationByName("JsonNotification").isPresent()
                || method.getAnnotationByName("JsonRequest").isPresent();
    }

    private static void printHeader(List<? extends TypeDeclaration<?>> segments) {
        out.format("# KeY-API%n%n");
    }

    private static void printFooter(List<? extends TypeDeclaration<?>> segments) {


    }


    private static boolean hasJsonSegment(TypeDeclaration<?> it) {
        return it.getAnnotationByName("JsonSegment").isPresent();
    }

    private static String getJsonSegment(TypeDeclaration<?> it) {
        var ae = it.getAnnotationByName("JsonSegment").get();
        return ae.asSingleMemberAnnotationExpr().getMemberValue()
                .asLiteralStringValueExpr().getValue();
    }
}
