/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.key.api.doc;/*
                                     * This file is part of KeY - https://key-project.org
                                     * KeY is licensed under the GNU General Public License Version
                                     * 2
                                     * SPDX-License-Identifier: GPL-2.0-only
                                     */

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
public abstract class PythonGenerator implements Supplier<String> {
    protected final Metamodel.KeyApi metamodel;
    protected PrintWriter out;
    protected final StringWriter target = new StringWriter();

    public PythonGenerator(Metamodel.KeyApi metamodel) {
        this.metamodel = metamodel;
    }

    @Override
    public String get() {
        try (var out = new PrintWriter(target)) {
            this.out = out;
            run();
        }
        return target.toString();
    }

    protected abstract void run();

    protected String asPython(String typeName) {
        return switch (typeName) {
        case "INT", "LONG" -> "int";
        case "STRING" -> "str";
        case "BOOL" -> "bool";
        case "DOUBLE" -> "float";
        default -> {
            var t = findType(typeName);
            yield asPython(t);
        }
        };
    }

    protected String asPython(Metamodel.Type t) {
        if (t instanceof Metamodel.ListType lt) {
            return "typing.List[" + asPython(lt.type()) + "]";
        }

        if (t instanceof Metamodel.EitherType lt) {
            return "typing.Union[" + asPython(lt.a()) + ", " + asPython(lt.b()) + "]";
        }

        if (t instanceof Metamodel.BuiltinType bt) {
            return switch (bt) {
            case INT, LONG -> "int";
            case STRING -> "str";
            case BOOL -> "bool";
            case DOUBLE -> "float";
            };
        }
        return t.name();
    }

    protected Metamodel.Type findType(String typeName) {
        return this.metamodel.types().stream().filter(it -> it.name().equals(typeName)).findFirst()
                .orElseThrow(() -> new RuntimeException("Could not find type: " + typeName));
    }


    public static class PyApiGen extends PythonGenerator {
        public PyApiGen(Metamodel.KeyApi metamodel) {
            super(metamodel);
        }

        @Override
        protected void run() {
            out.format("""
                    from __future__ import annotations
                    from .keydata import *
                    from .rpc import ServerBase, LspEndpoint

                    import enum
                    import abc
                    import typing
                    from abc import abstractmethod
                    """);
            server(
                metamodel.endpoints()
                        .stream()
                        .filter(it -> it instanceof Metamodel.ServerRequest
                                || it instanceof Metamodel.ServerNotification)
                        .sorted(Comparator.comparing(Metamodel.Endpoint::name)));

            client(
                metamodel.endpoints()
                        .stream()
                        .filter(it -> it instanceof Metamodel.ClientRequest
                                || it instanceof Metamodel.ClientNotification)
                        .sorted(Comparator.comparing(Metamodel.Endpoint::name)));
        }


        private void client(Stream<Metamodel.Endpoint> sorted) {
            out.format("class Client(abc.ABCMeta):%n");
            sorted.forEach(this::clientEndpoint);
        }

        private void clientEndpoint(Metamodel.Endpoint endpoint) {
            var args = endpoint.args().stream()
                    .map(it -> "%s : %s".formatted(it.name(), asPython(it.type())))
                    .collect(Collectors.joining(", "));
            out.format("    @abstractmethod%n");
            if (endpoint instanceof Metamodel.ClientRequest sr) {
                out.format("    def %s(self, %s) -> %s:%n", endpoint.name().replace("/", "_"), args,
                    asPython(sr.returnType()));
            } else {
                out.format("    def %s(self, %s):%n", endpoint.name().replace("/", "_"), args);
            }
            out.format("        \"\"\"%s\"\"\"%n%n", endpoint.documentation());
            out.format("        pass");
            out.println();
            out.println();
        }

        private void server(Stream<Metamodel.Endpoint> sorted) {
            out.format("""
                    class KeyServer(ServerBase):%n
                        def __init__(self, endpoint : LspEndpoint):
                            super().__init__(endpoint)

                    """);
            sorted.forEach(this::serverEndpoint);
        }

        private void serverEndpoint(Metamodel.Endpoint endpoint) {
            var args = endpoint.args().stream()
                    .map(it -> "%s : %s".formatted(it.name(), asPython(it.type())))
                    .collect(Collectors.joining(", "));

            var params = "[]";
            if (!endpoint.args().isEmpty()) {
                params = endpoint.args().stream()
                        .map(Metamodel.Argument::name)
                        .collect(Collectors.joining(" , ", "[", "]"));
            }

            if (endpoint instanceof Metamodel.ServerRequest sr) {
                out.format("    def %s(self, %s) -> %s:%n", endpoint.name().replace("/", "_"), args,
                    asPython(sr.returnType()));
                out.format("       \"\"\"%s\"\"\"%n%n", sr.documentation());
                out.format(
                    "       return self._call_sync(\"%s\", %s)".formatted(endpoint.name(), params));
            } else {
                out.format("    def %s(self, %s):%n", endpoint.name().replace("/", "_"), args);
                out.format("        \"\"\"%s\"\"\"%n%n", endpoint.documentation());
                out.format("        return self._call_async(\"%s\", %s)".formatted(endpoint.name(),
                    params));
            }
            out.println();
            out.println();
        }

    }


    public static class PyDataGen extends PythonGenerator {
        public PyDataGen(Metamodel.KeyApi metamodel) {
            super(metamodel);
        }

        @Override
        public String get() {
            try (var out = new PrintWriter(target)) {
                this.out = out;
                run();
            }
            return target.toString();
        }

        protected void run() {
            out.format("""
                    from __future__ import annotations
                    import enum
                    import abc
                    import typing
                    from abc import abstractmethod, ABCMeta

                    """);
            metamodel.types().forEach(this::printType);

            var names =
                metamodel.types().stream()
                        .map(it -> "\"%s\": %s".formatted(it.identifier(), it.name()))
                        .collect(Collectors.joining(","));
            out.format("KEY_DATA_CLASSES = { %s }%n%n", names);
            var names_reverse =
                metamodel.types().stream()
                        .map(it -> "\"%s\": \"%s\"".formatted(it.name(), it.identifier()))
                        .collect(Collectors.joining(","));
            out.format("KEY_DATA_CLASSES_REV = { %s }%n%n", names_reverse);
        }

        private void printType(Metamodel.Type type) {
            if (type instanceof Metamodel.ObjectType ot) {
                out.format("class %s:%n".formatted(type.name()));
                out.format("    \"\"\"%s\"\"\"%n", type.documentation());
                ot.fields().forEach(it -> out.format("%n    %s : %s%n    \"\"\"%s\"\"\"%n"
                        .formatted(it.name(), asPython(it.type()), it.documentation())));

                out.format("\n    def __init__(self%s):%n".formatted(
                    ot.fields().stream()
                            .map(Metamodel.Field::name)
                            .collect(Collectors.joining(", ", ", ", ""))));

                if (ot.fields().isEmpty())
                    out.format("        pass%n%n");

                for (Metamodel.Field field : ot.fields()) {
                    out.format("        self.%s = %s%n", field.name(), field.name());
                }

            } else if (type instanceof Metamodel.EnumType et) {
                out.format("class %s(enum.Enum):%n".formatted(type.name()));
                out.format("    \"\"\"%s\"\"\"%n%n", type.documentation());
                et.values().forEach(it -> out.format("    %s = None%n".formatted(it)));
            }
            out.println();
        }
    }
}
