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

/**
 * @author Alexander Weigl
 * @version 1 (29.10.23)
 */
public class DocGen implements Supplier<String> {
    private final Metamodel.KeyApi metamodel;
    private PrintWriter out;

    public DocGen(Metamodel.KeyApi metamodel) {
        this.metamodel = metamodel;
    }

    @Override
    public String get() {
        final StringWriter target = new StringWriter();
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
        var direction = switch (endpoint) {
        case Metamodel.ServerRequest sr -> "client -> server";
        case Metamodel.ClientRequest sr -> "server -> client";
        case Metamodel.ServerNotification sr -> "client ~~> server";
        case Metamodel.ClientNotification sr -> "server ~~> client";
        };

        out.format("### %s (`%s`) %n%n", endpoint.name(), direction);
        out.format("```%n");
        var args = endpoint.args();
        final var a = args.stream()
                .map(it -> "%s : %s".formatted(it.name(), it.type()))
                .collect(Collectors.joining(", "));
        switch (endpoint) {
        case Metamodel.ServerRequest sr ->
            out.format("Server.%s( %s ) -> %s%n", endpoint.name(), a, sr.returnType().name());
        case Metamodel.ClientRequest sr ->
            out.format("Client.%s( %s ) -> %s%n", endpoint.name(), a, sr.returnType().name());
        case Metamodel.ServerNotification ignored ->
            out.format("Server.%s( %s ) **async**%n", endpoint.name(), a);
        case Metamodel.ClientNotification ignored ->
            out.format("Client.%s( %s ) **async**%n", endpoint.name(), a);
        default -> {
        }
        }
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
                    """.formatted(type.name(), String.join(", ", et.values())));
            out.format(type.documentation());
        }
        out.format(type.documentation());
        out.println();
    }
}
