/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.doc;

import java.util.Arrays;
import java.util.Comparator;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uka.ilkd.key.nparser.varexp.TacletBuilderCommand;
import de.uka.ilkd.key.nparser.varexp.TacletBuilderCommandInfo;
import de.uka.ilkd.key.nparser.varexp.TacletBuilderManipulators;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.therapi.runtimejavadoc.CommentFormatter;
import com.google.common.collect.Streams;
import org.jspecify.annotations.Nullable;

/**
 *
 * @author Alexander Weigl
 * @version 1 (23.08.26)
 */
public class VarcondDoc {
    // region
    public static void main(String[] args) {
        var config = new ParserConfiguration();
        config.setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_21);
        StaticJavaParser.setConfiguration(config);

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
            System.out.println();
            System.out.println();
            System.out.format("### `%s`\n\n", name);
            cmds.sort(reversed);

            final var generalDocumentation = cmds.getFirst().getGeneralDocumentation();
            System.out.println(
                cleanJavadoc(new CommentFormatter().format(generalDocumentation.getComment())));

            System.out.format("\n**Signatures**\n\n");
            for (TacletBuilderCommandInfo cmd : cmds) {

                final var arguments = Streams.zip(
                    Arrays.stream(cmd.argNames()),
                    Arrays.stream(cmd.argumentTypes()).map(Enum::toString),
                    "%s: %s"::formatted)
                        .collect(Collectors.joining(", "));
                System.out.printf("* `%s(%s)`\n", name, arguments);

                if (cmd.isNegationSupported()) {
                    System.out.printf("* `\\not%s(%s)`\n", name, arguments);
                }

                System.out.println();
                final var argumentInformation = cmd.getArgumentInformation();

                System.out.println(
                    indent("   ", cleanJavadoc(argumentInformation.getComment().toString())));
                System.out.println();
                argumentInformation.getParams().stream()
                        .map(tag -> "   * `%s` %s".formatted(tag.getName(), tag.getComment()))
                        .forEach(System.out::println);
                System.out.println();
            }
        }
    }

    private static String indent(String spaces, String it) {
        return spaces + it.replace("\n", "\n" + spaces);
    }

    private static String cleanJavadoc(@Nullable String it) {
        if (it == null)
            it = "";
        return it.replace("<tt>", "`")
                .replace("<ul>", "\n")
                .replace("</ul>", "\n")
                .replace("<ul>", "\n")
                .replace("<li>", "* ")
                .replace("</li>", "")
                .replace("{@link", "`")
                .replace("}", "`")
                .replace("<code>", "`")
                .replace("</tt>", "`")
                .replace("</code>", "`")
                .replace("<b>", "**")
                .replace("</b>", "**");
    }
    // endregion
}
