/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.doc;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uka.ilkd.key.nparser.varexp.TacletBuilderCommand;
import de.uka.ilkd.key.nparser.varexp.TacletBuilderCommandInfo;
import de.uka.ilkd.key.nparser.varexp.TacletBuilderManipulators;

import com.github.therapi.runtimejavadoc.CommentFormatter;

/**
 * Generates the markdown documentation of all variable conditions (varconds) registered in
 * {@link TacletBuilderManipulators}, extracted from the javadocs of the implementing classes.
 *
 * @author Alexander Weigl
 * @version 1 (23.08.26)
 */
public class VarcondDoc extends AbstractDocGenerator {

    public static void main(String[] args) throws Exception {
        new VarcondDoc().run(args[0], args[1]);
    }

    @Override
    protected List<DocItem> collectData() {
        var items = new ArrayList<DocItem>();
        for (var entry : collectVarconds().entrySet()) {
            String name = entry.getKey();
            List<TacletBuilderCommandInfo> cmds = entry.getValue();

            final var generalDocumentation = cmds.getFirst().getGeneralDocumentation();
            String documentation =
                cleanJavadoc(new CommentFormatter().format(generalDocumentation.getComment()));

            var signatures = new ArrayList<DocSignature>();
            for (TacletBuilderCommandInfo cmd : cmds) {
                signatures.add(collectSignature(cmd));
            }

            items.add(new DocItem(name, documentation, signatures, null, false));
        }
        return items;
    }

    /// Builds the data of a single signature of a variable condition, i.e. of one registered
    /// command with the same (normalized) trigger name.
    private static DocSignature collectSignature(TacletBuilderCommandInfo cmd) {
        final var argumentInformation = cmd.getArgumentInformation();
        final var params = argumentInformation.getParams();

        var parameters = new ArrayList<DocParameter>();
        for (var i = 0; i < cmd.argumentTypes().length; i++) {
            String description = null;
            if (i < params.size()) {
                final var comment = params.get(i).getComment();
                description = cleanJavadoc(comment == null ? null : comment.toString());
            }
            parameters.add(new DocParameter(cmd.argNames()[i], cmd.argumentTypes()[i].toString(),
                description, null, false, null, false));
        }
        // Javadoc parameter tags beyond the declared argument list (e.g. `negated`) carry no
        // type, but their documentation is kept so that it is not lost.
        for (var i = cmd.argumentTypes().length; i < params.size(); i++) {
            final var comment = params.get(i).getComment();
            parameters.add(new DocParameter(params.get(i).getName(), null,
                cleanJavadoc(comment == null ? null : comment.toString()), null, false, null,
                false));
        }
        return new DocSignature(parameters,
            cleanJavadoc(argumentInformation.getComment().toString()),
            cmd.isNegationSupported());
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
