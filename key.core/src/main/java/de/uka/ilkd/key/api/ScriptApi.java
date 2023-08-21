/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.api;

import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.macros.scripts.EngineState;
import de.uka.ilkd.key.macros.scripts.ProofScriptCommand;
import de.uka.ilkd.key.macros.scripts.ScriptException;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;

import org.key_project.util.collection.ImmutableList;

/**
 * This API class offers methods to apply script commands and match commands
 *
 * @author Alexander Weigl
 * @author S. Grebing
 */
public class ScriptApi {
    private final ProofApi api;
    private final EngineState state;
    private final Matcher matcher;

    public ScriptApi(ProofApi proofApi) {
        api = proofApi;
        state = new EngineState(api.getProof());
        matcher = new Matcher(api);
    }

    /**
     * Matches a sequent against a sequent pattern (a schematic sequent) returns a list of Nodes
     * containing matching results from where the information about instantiated schema variables
     * can be extracted. If no match was possible the list is exmpt.
     *
     * @param pattern a string representation of the pattern sequent against which the current
     *        sequent should be matched
     * @param currentSeq current concrete sequent
     * @param assignments variables appearing in the pattern as schemavariables with their
     *        corresponding type in KeY
     * @return List of VariableAssignments (possibly empty if no match was found)
     */
    public List<VariableAssignments> matchPattern(String pattern, Sequent currentSeq,
            VariableAssignments assignments) {
        return matcher.matchPattern(pattern, currentSeq, assignments);
    }

    /**
     * Execute ScriptCommand onto goal node
     *
     * @param command to be applied with parameters set
     * @return List of new proof goals (possibly empty) Should throw an Exception if command not
     *         applicable?
     */
    public <T> ScriptResults executeScriptCommand(ProofScriptCommandCall<T> call,
            ProjectedNode onNode) throws ScriptException, InterruptedException {
        // TODO VariableAssignments should be in instantiateCommand

        state.setGoal(onNode.getProofNode());
        call.command.execute((AbstractUserInterfaceControl) api.getEnv().getUi(), call.parameter,
            state);

        ImmutableList<Goal> goals = api.getProof().getSubtreeGoals(onNode.getProofNode());
        // TODO filter for open goals if necessary
        ScriptResults sr = new ScriptResults();

        goals.forEach(g -> sr.add(ScriptResult.create(g.node(), onNode, call)));

        return sr;
    }

    /**
     * Evaluate the arguments passed to a command
     *
     * @param arguments
     * @param <T>
     * @return
     */
    public <T> ProofScriptCommandCall<T> instantiateCommand(ProofScriptCommand<T> command,
            Map<String, String> arguments) throws Exception {
        return new ProofScriptCommandCall<>(command, command.evaluateArguments(state, arguments));
    }


    /**
     *
     * @param term
     * @param assignments
     * @return
     * @throws Exception either for Syntax or Type error
     */
    public Term toTerm(String term, VariableAssignments assignments) throws Exception {
        // TODO
        return null;
    }

    /**
     * ~> Beweisbaum -> Shallow Copy hier implementieren
     *
     * @param root
     * @param end
     * @return
     */
    public ProjectedNode getIntermediateTree(ScriptResults root, ScriptResults end) {
        /*
         * Baum suche, startet bei allen Nodes von root.
         *
         * Endet sobald ein Node von end erreicht ist.
         */
        ProjectedNode pseudoRoot = ProjectedNode.pseudoRoot();
        Queue<Node> queue = new LinkedList<>();
        root.forEach(r -> queue.add(r.getProjectedNode().getProofNode()));

        while (!queue.isEmpty()) {

        }


        return pseudoRoot;
    }


}
