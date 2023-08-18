/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts;

import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.macros.scripts.meta.Option;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.TacletApp;

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
public class SaveNewNameCommand extends AbstractCommand<SaveNewNameCommand.Parameters> {
    public SaveNewNameCommand() {
        super(Parameters.class);
    }

    @Override
    public Parameters evaluateArguments(EngineState state, Map<String, String> arguments)
            throws Exception {
        return state.getValueInjector().inject(this, new Parameters(), arguments);
    }

    @Override
    public void execute(AbstractUserInterfaceControl uiControl, Parameters params,
            EngineState stateMap) throws ScriptException, InterruptedException {

        if (!params.abbreviation.startsWith("@")) {
            throw new ScriptException(
                "Unexpected parameter to saveNewName, only @var allowed: " + params.abbreviation);
        }

        final AbbrevMap abbrMap = stateMap.getAbbreviations();
        final String key = params.abbreviation.substring(1);
        final String stringToMatch = params.matches;

        try {
            final Goal goal = stateMap.getFirstOpenAutomaticGoal();
            final Node node = goal.node().parent();
            final List<String> matches =
                node.getNameRecorder().getProposals().stream().map(Name::toString)
                        .filter(str -> str.matches(stringToMatch)).collect(Collectors.toList());

            if (matches.size() != 1) {
                throw new ScriptException(
                    String.format("Found %d matches for expression %s in new names, expected 1",
                        matches.size(), stringToMatch));
            }

            final Named lookupResult = goal.getLocalNamespaces().lookup(new Name(matches.get(0)));

            assert lookupResult != null;

            // Should be a function or program variable
            final TermBuilder tb = //
                stateMap.getProof().getServices().getTermBuilder();
            final Term t;
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

    public static class Parameters {
        @Option(value = "#2", required = true)
        public String abbreviation;
        @Option(value = "matches", required = true)
        public String matches;
    }

    @Override
    public String getName() {
        return "saveNewName";
    }
}
