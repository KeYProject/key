import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.Comparator;
import java.util.function.Supplier;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * @author Alexander Weigl
 * @version 1 (29.10.23)
 */
public class PyGen implements Supplier<String> {
    private final Metamodel.KeyApi metamodel;
    private PrintWriter out;
    private final StringWriter target = new StringWriter();

    public PyGen(Metamodel.KeyApi metamodel) {
        this.metamodel = metamodel;
    }

    @Override
    public String get() {
        try (var out = new PrintWriter(target)) {
            this.out = out;

            out.format("""
                    import enum
                    import abc
                    import typing
                    from abc import abstractmethod                    
                    """);

            metamodel.types().forEach(this::printType);
            server(
                    metamodel.endpoints()
                            .stream()
                            .filter(it -> it instanceof Metamodel.ServerRequest || it instanceof Metamodel.ServerNotification)
                            .sorted(Comparator.comparing(Metamodel.Endpoint::name)));

            client(
                    metamodel.endpoints()
                            .stream()
                            .filter(it -> it instanceof Metamodel.ClientRequest || it instanceof Metamodel.ClientNotification)
                            .sorted(Comparator.comparing(Metamodel.Endpoint::name)));

        }
        return target.toString();
    }

    private void client(Stream<Metamodel.Endpoint> sorted) {
        out.format("class Client(abc.AbcMeta):%n");
        sorted.forEach(this::clientEndpoint);
    }

    private void clientEndpoint(Metamodel.Endpoint endpoint) {
        var args = endpoint.args().stream()
                .map(it -> "%s : %s".formatted(it.name(), asPython(it.type())))
                .collect(Collectors.joining(", "));
        out.format("    @abstractmethod%n");
        if (endpoint instanceof Metamodel.ClientRequest sr) {
            out.format("    def %s(self, %s) -> %s:%n", endpoint.name().replace("/", "_"), args, asPython(sr.returnType()));
        } else {
            out.format("    def %s(self, %s):%n", endpoint.name().replace("/", "_"), args);
        }
        out.format("        \"\"\"%s\"\"\"%n%n", endpoint.documentation());
        out.format("        pass".formatted(endpoint.name(), ""));
        out.println();
        out.println();
    }

    private void server(Stream<Metamodel.Endpoint> sorted) {
        out.format("class KeyServer():%n");
        sorted.forEach(this::serverEndpoint);
    }

    private void serverEndpoint(Metamodel.Endpoint endpoint) {
        var args = endpoint.args().stream()
                .map(it -> "%s : %s".formatted(it.name(), asPython(it.type())))
                .collect(Collectors.joining(", "));
        if (endpoint instanceof Metamodel.ServerRequest sr) {
            out.format("    def %s(self, %s) -> %s:%n", endpoint.name().replace("/", "_"), args,
                    asPython(sr.returnType()));
            out.format("       \"\"\"%s\"\"\"%n%n", sr.documentation());
            out.format("       return self.rpc.call_sync(\"%s\", %s)".formatted(endpoint.name(), ""));
        } else {
            out.format("    def %s(self, %s):%n", endpoint.name().replace("/", "_"), args);
            out.format("        \"\"\"%s\"\"\"%n%n", endpoint.documentation());
            out.format("        return self.rpc.call_async(\"%s\", %s)".formatted(endpoint.name(), ""));
        }
        out.println();
        out.println();
    }

    private void printType(Metamodel.Type type) {
        if (type instanceof Metamodel.ObjectType ot) {
            out.format("class %s:%n".formatted(type.name()));
            out.format("    \"\"\"%s\"\"\"%n%n", type.documentation());
            ot.fields().forEach(it -> out.format("    %s : %s%n".formatted(it.name(), asPython(it.type()))));
        } else if (type instanceof Metamodel.EnumType et) {
            out.format("class %s(enum.Enum):%n".formatted(type.name()));
            out.format("    \"\"\"%s\"\"\"%n%n", type.documentation());
            et.values().forEach(it -> out.format("    %s = None%n".formatted(it)));
        }
        out.println();
    }

    private String asPython(String typeName) {
        return switch (typeName) {
            case "INT" -> "int";
            case "LONG" -> "int";
            case "STRING" -> "str";
            case "BOOL" -> "bool";
            case "DOUBLE" -> "float";
            default -> {
                var t = findType(typeName);
                yield asPython(t);
            }
        };
    }

    private String asPython(Metamodel.Type t) {
        if (t instanceof Metamodel.ListType lt) {
            return "typing.List[" + asPython(lt.type()) + "]";
        }

        if (t instanceof Metamodel.EitherType lt) {
            return "typing.Union[" + asPython(lt.a()) + ", " + asPython(lt.b()) + "]";
        }
        return t.name();
    }

    private Metamodel.Type findType(String typeName) {
        return this.metamodel.types().stream().filter(it -> it.name().equals(typeName)).findFirst()
                .orElseThrow(() -> new RuntimeException("Could not find type: " + typeName));
    }
}