/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.doc;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.lang.reflect.Parameter;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uka.ilkd.key.rule.metaconstruct.ProgramTransformer;
import de.uka.ilkd.key.rule.metaconstruct.TransformerMeta;

import com.github.therapi.runtimejavadoc.ClassJavadoc;
import com.github.therapi.runtimejavadoc.CommentFormatter;
import com.github.therapi.runtimejavadoc.RuntimeJavadoc;
import com.google.common.collect.Streams;

public class CodeTransformerDoc extends AbstractDocGenerator {
    public static void main(String[] args) throws Exception {
        new CodeTransformerDoc().run(args[0], args[1]);
    }

    @Override
    protected void generateDocumentation(PrintStream out) throws IOException {
        for (Class<?> entry : collectTransformers()) {
            out.println();
            out.println();


            final var annotation = entry.getAnnotation(TransformerMeta.class);
            String name;
            if (annotation != null) {
                name = annotation.name();
            } else
                continue;

            out.format("### `%s`\n\n", name);

            ClassJavadoc classDoc = RuntimeJavadoc.getJavadoc(entry);
            out.println(cleanJavadoc(new CommentFormatter().format(classDoc.getComment())));

            out.format("\n**Signatures**\n\n");
            for (var constr : entry.getConstructors()) {
                final var arguments = Streams.zip(
                    Arrays.stream(constr.getParameters())
                            .map(Parameter::getName),
                    Arrays.stream(constr.getParameters())
                            .map(Parameter::getType)
                            .map(Class::getCanonicalName),
                    "%s: %s"::formatted)
                        .collect(Collectors.joining(", "));
                out.printf("* `%s(%s)`\n", name, arguments);

                out.println();
                final var argumentInformation = RuntimeJavadoc.getJavadoc(constr);

                out.println(
                    indent("   ", cleanJavadoc(argumentInformation.getComment().toString())));
                out.println();
                argumentInformation.getParams().stream()
                        .map(tag -> "   * `%s` %s".formatted(tag.getName(), tag.getComment()))
                        .forEach(out::println);
                out.println();
            }
        }
    }

    @Override
    protected Object generateJsonData() throws IOException {
        var varconds = new ArrayList<Map<String, Object>>();
        for (Class<?> entry : collectTransformers()) {
            final var annotation = entry.getAnnotation(TransformerMeta.class);
            String name;
            if (annotation != null) {
                name = annotation.name();
            } else
                continue;

            var transformer = new LinkedHashMap<String, Object>();
            varconds.add(transformer);
            transformer.put("name", name);
            transformer.put("doc",
                RuntimeJavadoc.getJavadoc(entry).getComment().toString());
            var c = new ArrayList<>();
            transformer.put("signatures", c);
            for (var constr : entry.getConstructors()) {
                var d = new HashMap<>();
                c.add(d);
                d.put("paramNames", Arrays.stream(constr.getParameters())
                        .map(Parameter::getName).toList());
                d.put("paramTypes",
                    Arrays.stream(constr.getParameters())
                            .map(Parameter::getType)
                            .map(Class::getCanonicalName).toList());
                final var argumentInformation = RuntimeJavadoc.getJavadoc(constr);
                d.put("documentation",
                    cleanJavadoc(argumentInformation.getComment().toString()));
            }
        }
        return varconds;
    }

    private List<? extends Class<?>> collectTransformers() throws IOException {
        String path = ProgramTransformer.class.getPackageName().replace('.', '/');
        Set<String> names = new TreeSet<>();

        for (String entry : System.getProperty("java.class.path", "").split(File.pathSeparator)) {
            var file = Paths.get(entry);
            if (Files.isRegularFile(file) && entry.endsWith(".jar")) {
                try (var fs = FileSystems.newFileSystem(file, Collections.emptyMap())) {
                    var folder = fs.getRootDirectories().iterator().next();
                    names.addAll(scan(folder, path));
                }
            } else if (Files.isDirectory(file)) {
                names.addAll(scan(file, path));
            }
        }

        return names.stream().map(className -> {
            try {
                return (Class<?>) Class.forName(className);
            } catch (ClassNotFoundException e) {
                System.err.format("No class found %s possible%n", className);
                return null;
            }
        }).filter(Objects::nonNull).toList();
    }

    private static List<String> scan(Path root, String packageName)
            throws IOException {
        var packageFolder = root.resolve(packageName);
        if (Files.exists(packageFolder) && Files.isDirectory(packageFolder)) {
            try (Stream<Path> files = Files.walk(packageFolder)) {
                return files.filter(Files::isRegularFile)
                        .filter(it -> it.toString().endsWith(".class"))
                        .filter(it -> !it.toString().contains("$"))
                        .map(p -> root.relativize(p)
                                .toString()
                                .replace('\\', '/').replace('/', '.'))
                        .map(rel -> rel.replace(".class", ""))
                        .toList();
            }
        }
        return Collections.emptyList();
    }
}
