/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.doc;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uka.ilkd.key.nparser.varexp.TacletBuilderCommand;
import de.uka.ilkd.key.nparser.varexp.TacletBuilderCommandInfo;
import de.uka.ilkd.key.nparser.varexp.TacletBuilderManipulators;

import com.github.therapi.runtimejavadoc.CommentFormatter;
import com.google.common.collect.Streams;

/**
 * Generates the markdown documentation of all variable conditions (varconds) registered in
 * {@link TacletBuilderManipulators}, extracted from the javadocs of the implementing classes.
 *
 * @author Alexander Weigl
 * @version 1 (23.08.26)
 */
public class VarcondDoc extends AbstractDocGenerator {

    public static void main(String[] args) throws Exception {
        new VarcondDoc().run(args);
    }

    @Override
    protected void generateDocumentation(PrintStream out) {
        for (var entry : collectVarconds().entrySet()) {
            String name = entry.getKey();
            List<TacletBuilderCommandInfo> cmds = entry.getValue();

            out.println();
            out.println();
            out.format("### `%s`\n\n", name);

            final var generalDocumentation = cmds.getFirst().getGeneralDocumentation();
            out.println(
                cleanJavadoc(new CommentFormatter().format(generalDocumentation.getComment())));

            out.format("\n**Signatures**\n\n");
            for (TacletBuilderCommandInfo cmd : cmds) {

                final var arguments = Streams.zip(
                    Arrays.stream(cmd.argNames()),
                    Arrays.stream(cmd.argumentTypes()).map(Enum::toString),
                    "%s: %s"::formatted)
                        .collect(Collectors.joining(", "));
                out.printf("* `%s(%s)`\n", name, arguments);

                if (cmd.isNegationSupported()) {
                    out.printf("* `\\not%s(%s)`\n", name, arguments);
                }

                out.println();
                final var argumentInformation = cmd.getArgumentInformation();

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
    protected Object generateJsonData() {
        var varconds = new ArrayList<Map<String, Object>>();
        for (var entry : collectVarconds().entrySet()) {
            String name = entry.getKey();
            List<TacletBuilderCommandInfo> cmds = entry.getValue();

            var varcond = new LinkedHashMap<String, Object>();
            varcond.put("name", name);
            final var generalDocumentation = cmds.getFirst().getGeneralDocumentation();
            varcond.put("description",
                cleanJavadoc(new CommentFormatter().format(generalDocumentation.getComment())));

            var signatures = new ArrayList<Map<String, Object>>();
            for (TacletBuilderCommandInfo cmd : cmds) {
                final var argumentInformation = cmd.getArgumentInformation();
                var params = argumentInformation.getParams();

                var signature = new LinkedHashMap<String, Object>();
                signature.put("negated", cmd.isNegationSupported());
                signature.put("description",
                    cleanJavadoc(argumentInformation.getComment().toString()));

                var arguments = new ArrayList<Map<String, Object>>();
                for (var i = 0; i < cmd.argumentTypes().length; i++) {
                    var argument = new LinkedHashMap<String, Object>();
                    argument.put("name", cmd.argNames()[i]);
                    argument.put("type", cmd.argumentTypes()[i].toString());
                    if (i < params.size()) {
                        final var comment = params.get(i).getComment();
                        argument.put("description",
                            cleanJavadoc(comment == null ? null : comment.toString()));
                    }
                    arguments.add(argument);
                }
                signature.put("arguments", arguments);
                signatures.add(signature);
            }
            varcond.put("signatures", signatures);
            varconds.add(varcond);
        }
        return Map.of("varconds", varconds);
    }

    /// Collects all registered variable conditions, grouped and sorted by their trigger name;
    /// within a group, the signatures are sorted by the number of declared argument types
    /// (descending).
    private LinkedHashMap<String, List<TacletBuilderCommandInfo>> collectVarconds() {
        Function<String, String> normalizeCmdName =
            (String it) -> it.startsWith("\\") ? it.replace("\\\\", "\\") : "\\" + it;
        Function<TacletBuilderCommandInfo, String> getTriggerName = TacletBuilderCommandInfo::name;

        var grouped = TacletBuilderManipulators.getConditionBuilders().stream()
                .map(TacletBuilderCommand::getInformation)
                .collect(Collectors.groupingBy(getTriggerName.andThen(normalizeCmdName)));
        Comparator<TacletBuilderCommandInfo> reversed =
            Comparator.comparing((TacletBuilderCommandInfo it) -> it.argumentTypes().length)
                    .reversed();

        var result = new LinkedHashMap<String, List<TacletBuilderCommandInfo>>();
        grouped.keySet().stream().sorted().forEach(
            name -> {
                var cmds = grouped.get(name);
                cmds.sort(reversed);
                result.put(name, cmds);
            });
        return result;
    }
}
