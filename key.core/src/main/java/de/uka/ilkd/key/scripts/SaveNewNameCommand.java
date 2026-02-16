/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import java.util.List;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.scripts.meta.Argument;
import de.uka.ilkd.key.scripts.meta.Documentation;
import de.uka.ilkd.key.scripts.meta.Option;

import org.key_project.logic.Name;
import org.key_project.logic.Named;
import org.key_project.logic.op.Function;

/**
 * Special "Let" usually to be applied immediately after a manual rule application. Saves a new name
 * introduced by the last {@link TacletApp} which matches certain criteria into an abbreviation for
 * later use. A nice use case is a manual loop invariant rule application, where the newly
 * introduced anonymizing Skolem constants can be saved for later interactive instantiations. As for
 * the {@link LetCommand}, it is not allowed to call this command multiple times with the same name
 * argument (all names used for remembering instantiations are "final").
 *
 * @author Dominic Steinhoefel
 */
public class SaveNewNameCommand extends AbstractCommand {
    public SaveNewNameCommand() {
        super(Parameters.class);
    }

    @Override
    public void execute(ScriptCommandAst arguments) throws ScriptException, InterruptedException {
        var params = state().getValueInjector().inject(new Parameters(), arguments);
        if (!params.abbreviation.startsWith("@")) {
            throw new ScriptException(
                "Unexpected parameter to saveNewName, only @var allowed: " + params.abbreviation);
        }

        final AbbrevMap abbrMap = state().getAbbreviations();
        final String key = params.abbreviation.substring(1);
        final String stringToMatch = params.matches;

        try {
            final Goal goal = state().getFirstOpenAutomaticGoal();
            final Node node = goal.node().parent();
            final List<String> matches =
                node.getNameRecorder().getProposals().stream().map(Name::toString)
                        .filter(str -> str.matches(stringToMatch)).toList();

            if (matches.size() != 1) {
                throw new ScriptException(
                    String.format("Found %d matches for expression %s in new names, expected 1",
                        matches.size(), stringToMatch));
            }

            final Named lookupResult =
                goal.getLocalNamespaces().lookup(new Name(matches.getFirst()));

            assert lookupResult != null;

            // Should be a function or program variable
            final TermBuilder tb = //
                state().getProof().getServices().getTermBuilder();
            final JTerm t;
            if (lookupResult instanceof Function) {
                t = tb.func((Function) lookupResult);
            } else if (lookupResult instanceof ProgramVariable) {
                t = tb.var((ProgramVariable) lookupResult);
            } else {
                throw new ScriptException(
                    String.format("Unexpected instantiation type in SaveNewName: %s",
                        lookupResult.getClass().getSimpleName()));
            }

            if (abbrMap.containsAbbreviation(key)) {
                abbrMap.changeAbbrev(key, t, true);
            } else {
                abbrMap.put(t, key, true);
            }
        } catch (Exception e) {
            throw new ScriptException(e);
        }
    }

    @Documentation(category = "Internal", value = """
        Special "Let" usually to be applied immediately after a manual rule application. Saves a new name
        introduced by the last rule which matches certain criteria into an abbreviation for
        later use. A nice use case is a manual loop invariant rule application, where the newly
        introduced anonymizing Skolem constants can be saved for later interactive instantiations. As for
        the let command, it is not allowed to call this command multiple times with the same name
        argument (all names used for remembering instantiations are "final").
        """)
    public static class Parameters {
        @Documentation("The abbreviation to store the new name under, must start with @")
        @Argument
        public String abbreviation;

        @Documentation("A regular expression to match the new name against, must match exactly one name")
        @Option(value = "matches")
        public String matches;
    }

    @Override
    public String getName() {
        return "saveNewName";
    }
}
