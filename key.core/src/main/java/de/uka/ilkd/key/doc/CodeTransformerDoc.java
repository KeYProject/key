/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.doc;

import java.io.File;
import java.io.IOException;
import java.lang.reflect.Constructor;
import java.lang.reflect.Parameter;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Stream;

import de.uka.ilkd.key.rule.metaconstruct.ProgramTransformer;
import de.uka.ilkd.key.rule.metaconstruct.TransformerMeta;

import com.github.therapi.runtimejavadoc.ClassJavadoc;
import com.github.therapi.runtimejavadoc.CommentFormatter;
import com.github.therapi.runtimejavadoc.RuntimeJavadoc;

/**
 * Generates the documentation of all code transformers (program transformers and term
 * transformers) annotated with {@link TransformerMeta}, extracted from their Javadocs.
 *
 * @author Alexander Weigl
 * @version 1 (22.10.26)
 */
public class CodeTransformerDoc extends AbstractDocGenerator {

    public static void main(String[] args) throws Exception {
        new CodeTransformerDoc().run(args[0], args[1]);
    }

    @Override
    protected List<DocItem> collectData() throws IOException {
        var items = new ArrayList<DocItem>();
        for (Class<?> entry : collectTransformers()) {
            final var annotation = entry.getAnnotation(TransformerMeta.class);
            if (annotation == null) {
                continue;
            }
            String name = annotation.name();

            ClassJavadoc classDoc = RuntimeJavadoc.getJavadoc(entry);
            String documentation =
                cleanJavadoc(new CommentFormatter().format(classDoc.getComment()));

            var signatures = new ArrayList<DocSignature>();
            for (var constr : entry.getConstructors()) {
                signatures.add(collectSignature(constr));
            }
            items.add(new DocItem(name, documentation, signatures, null, false));
        }
        return items;
    }

    /// Builds the data of a single signature of a code transformer, i.e. of one of its
    /// constructors including the javadoc of the constructor and of its parameters.
    private static DocSignature collectSignature(Constructor<?> constr) {
        final var parameterNames =
            Arrays.stream(constr.getParameters()).map(Parameter::getName).toList();
        final var parameterTypes =
            Arrays.stream(constr.getParameters()).map(Parameter::getType)
                    .map(Class::getCanonicalName)
                    .toList();
        final var argumentInformation = RuntimeJavadoc.getJavadoc(constr);
        final var params = argumentInformation.getParams();

        var parameters = new ArrayList<DocParameter>();
        for (var i = 0; i < parameterNames.size(); i++) {
            // prefer the javadoc parameter name over the reflection name (`arg0`, `arg1`)
            String name = i < params.size() && !params.get(i).getName().isBlank()
                    ? params.get(i).getName()
                    : parameterNames.get(i);
            String description = null;
            if (i < params.size()) {
                final var comment = params.get(i).getComment();
                description = cleanJavadoc(comment == null ? null : comment.toString());
            }
            parameters.add(new DocParameter(name, parameterTypes.get(i), description, null,
                false, null, false));
        }
        return new DocSignature(parameters,
            cleanJavadoc(argumentInformation.getComment().toString()), false);
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
