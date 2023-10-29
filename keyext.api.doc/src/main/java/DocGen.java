import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.Comparator;
import java.util.function.Supplier;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (29.10.23)
 */
public class DocGen implements Supplier<String> {
    private final Metamodel.KeyApi metamodel;
    private PrintWriter out;
    private final StringWriter target = new StringWriter();

    public DocGen(Metamodel.KeyApi metamodel) {
        this.metamodel = metamodel;
    }

    @Override
    public String get() {
        try (var out = new PrintWriter(target)) {
            this.out = out;
            printHeader();

            out.format("## Types%n");
            metamodel.types()
                    .stream().sorted(Comparator.comparing(Metamodel.Type::name))
                    .forEach(this::printType);

            out.format("## Endpoints%n");
            metamodel.endpoints()
                    .stream().sorted(Comparator.comparing(Metamodel.Endpoint::name))
                    .forEach(this::endpoints);
            printFooter();
        }
        return target.toString();
    }

    private void printFooter() {

    }

    private void printHeader() {


    }

    private void endpoints(Metamodel.Endpoint endpoint) {
        //out.format("## Group: %s%n%n", getJsonSegment(typeDeclaration));
        //out.println(getJavaDoc(typeDeclaration));
        //out.println("\n");

        var direction = "";
        if (endpoint instanceof Metamodel.ServerRequest sr)
            direction = "client -> server";
        else if (endpoint instanceof Metamodel.ClientRequest sr)
            direction = "server -> client";
        else if (endpoint instanceof Metamodel.ServerNotification sr)
            direction = "client ~~> server";
        else if (endpoint instanceof Metamodel.ClientNotification sr)
            direction = "server ~~> client";

        out.format("### %s (`%s`) %n%n", endpoint.name(), direction);
        out.format("```%n");
        var args = endpoint.args();
        final var a = args.stream()
                .map(it -> "%s : %s".formatted(it.name(), it.type()))
                .collect(Collectors.joining(", "));
        if (endpoint instanceof Metamodel.ServerRequest sr) {
            out.format("Server.%s( %s ) -> %s%n", endpoint.name(), a, sr.returnType().name());
        } else if (endpoint instanceof Metamodel.ClientRequest sr)
            out.format("Client.%s( %s ) -> %s%n", endpoint.name(), a, sr.returnType().name());
        else if (endpoint instanceof Metamodel.ServerNotification sr)
            out.format("Server.%s( %s ) **async**%n", endpoint.name(), a);
        else if (endpoint instanceof Metamodel.ClientNotification sr)
            out.format("Client.%s( %s ) **async**%n", endpoint.name(), a);
        out.format("```%n");

        out.println(endpoint.documentation());
        out.println();
    }

    private void printType(Metamodel.Type type) {
        out.format("### Type: %s%n", type.name());
        if (type instanceof Metamodel.ObjectType ot) {
            out.format("""
                    ```
                    type %s {
                     %s
                    }
                    ```
                    """.formatted(type.name(),
                    ot.fields().stream().sorted(Comparator.comparing(Metamodel.Field::name))
                            .map(it -> "\t%s : %s".formatted(it.name(), it.type()))
                            .collect(Collectors.joining("\n"))));
        }

        if (type instanceof Metamodel.EnumType et) {
            out.format("""
                    ```
                    enum %s { %s }
                    ```
                    """.formatted(type.name(), String.join(", ", et.values())
            ));
            out.format(type.documentation());
        }
        out.format(type.documentation());
        out.println();
    }

        /*
        private static String getCallName (MethodDeclaration m, TypeDeclaration < ?>td){
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
        private static String getJavaDoc (NodeWithJavadoc < ? > typeDeclaration){
            if (typeDeclaration.getJavadoc().isPresent()) {
                final var javadoc = typeDeclaration.getJavadoc().get();
                return javadoc.getDescription().toText()
                        + "\n\n"
                        + javadoc.getBlockTags().stream().map(it -> "* " + it.toText())
                        .collect(Collectors.joining("\n"));
            }
            return "";
        }

        private static String type (MethodDeclaration method){
            if (method.getAnnotationByName("JsonNotification").isPresent())
                return "notification";
            if (method.getAnnotationByName("JsonRequest").isPresent())
                return "request";
            return "";
        }

        private static boolean isExported (MethodDeclaration method){
            return method.getAnnotationByName("JsonNotification").isPresent()
                    || method.getAnnotationByName("JsonRequest").isPresent();
        }

        private void printHeader () {
            out.format("# KeY-API%n%n");
        }

        private void printFooter () {
        }


    /*
    private static boolean hasJsonSegment(TypeDeclaration<?> it) {
        return it.getAnnotationByName("JsonSegment").isPresent();
    }

    private static String getJsonSegment(TypeDeclaration<?> it) {
        var ae = it.getAnnotationByName("JsonSegment").get();
        return ae.asSingleMemberAnnotationExpr().getMemberValue()
                .asLiteralStringValueExpr().getValue();
    }
     */

}

