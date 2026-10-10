/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.doc;

import java.io.PrintStream;
import java.util.Arrays;
import java.util.Comparator;
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
        Function<String, String> normalizeCmdName =
            (String it) -> it.startsWith("\\") ? it.replace("\\\\", "\\") : "\\" + it;
        Function<TacletBuilderCommandInfo, String> getTriggerName = TacletBuilderCommandInfo::name;

        var g = TacletBuilderManipulators.getConditionBuilders().stream()
                .map(TacletBuilderCommand::getInformation)
                .collect(Collectors.groupingBy(getTriggerName.andThen(normalizeCmdName)));
        Comparator<TacletBuilderCommandInfo> reversed =
            Comparator.comparing((TacletBuilderCommandInfo it) -> it.argumentTypes().length)
                    .reversed();

        var conds = g.keySet().stream().sorted().toList();

        for (var name : conds) {
            var cmds = g.get(name);
            out.println();
            out.println();
            out.format("### `%s`\n\n", name);
            cmds.sort(reversed);

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
}
