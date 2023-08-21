/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.api;

import java.util.*;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.match.legacy.LegacyTacletMatcher;

import org.key_project.util.collection.ImmutableList;

import org.antlr.v4.runtime.CharStreams;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Matcher to deal with matching a string pattern against a sequent
 *
 * @author S.Grebing
 */
public class Matcher {
    private static final Logger LOGGER = LoggerFactory.getLogger(Matcher.class);
    private final ProofApi api;

    /**
     * Creates a new matcher for the given proof and environment.
     *
     * @param api reference to proof api in order to get access to the key environment
     */
    public Matcher(ProofApi api) {
        this.api = api;
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
    // List of VarAssignment
    public List<VariableAssignments> matchPattern(String pattern, Sequent currentSeq,
            VariableAssignments assignments) {
        // copy services in order to not accidently set assignments and namespace for environment
        Services copyServices = api.getEnv().getServices().copy(false);
        // Aufbau der Deklarationen fuer den NameSpace
        buildNameSpace(assignments, copyServices);
        // Zusammenbau des Pseudotaclets
        // Parsen des Taclets
        String patternString = "matchPattern{\\assumes(" + pattern + ") \\find (==>)  \\add (==>)}";

        Taclet t = parseTaclet(patternString, copyServices);

        // Build Matcher for Matchpattern
        LegacyTacletMatcher ltm = new LegacyTacletMatcher(t);

        // patternSequent should not be null, as we have created it
        assert t.ifSequent() != null;
        Sequent patternSeq = t.ifSequent();
        int asize = patternSeq.antecedent().size();
        int size = asize + patternSeq.succedent().size();
        // Iterator durch die Pattern-Sequent

        List<SearchNode> finalCandidates = new ArrayList<>(100);
        if (size > 0) {
            // Iteratoren durch die Sequent
            ImmutableList<IfFormulaInstantiation> antecCand =
                IfFormulaInstSeq.createList(currentSeq, true, copyServices);
            ImmutableList<IfFormulaInstantiation> succCand =
                IfFormulaInstSeq.createList(currentSeq, false, copyServices);

            SequentFormula[] patternArray = new SequentFormula[patternSeq.size()];
            int i = 0;
            for (SequentFormula fm : patternSeq) {
                patternArray[i++] = fm;
            }


            Queue<SearchNode> queue = new LinkedList<>();
            // init
            queue.add(new SearchNode(patternArray, asize, antecCand, succCand));


            while (!queue.isEmpty()) {
                SearchNode node = queue.remove();
                boolean inAntecedent = node.isAntecedent();
                LOGGER.debug(inAntecedent ? "In Antec: " : "In Succ");

                IfMatchResult ma = ltm.matchIf((inAntecedent ? antecCand : succCand),
                    node.getPatternTerm(), node.mc, copyServices);

                if (!ma.getMatchConditions().isEmpty()) {
                    ImmutableList<MatchConditions> testma = ma.getMatchConditions();

                    for (MatchConditions matchConditions : testma) {
                        SearchNode sn = new SearchNode(node, matchConditions);
                        if (sn.isFinished()) {
                            finalCandidates.add(sn);
                        } else {
                            queue.add(sn);
                        }
                    }
                } else {
                    LOGGER.debug("Pattern Empty");
                }
            }
        }
        List<VariableAssignments> matches = new ArrayList<>();
        if (!finalCandidates.isEmpty()) {
            for (SearchNode finalCandidate : finalCandidates) {
                VariableAssignments va = extractAssignments(finalCandidate, assignments);
                matches.add(va);
            }
        }
        return matches;
    }

    /**
     * Extract the matching results from each SearchNode and tranform these to Variable Assigments
     *
     * @param sn SearchNode
     * @return VariableAssigments containing the assignments fo matching results to schemavariables
     */
    private VariableAssignments extractAssignments(SearchNode sn, VariableAssignments assignments) {
        VariableAssignments va = new VariableAssignments();
        SVInstantiations insts = sn.mc.getInstantiations();
        Set<String> varNames = assignments.getTypeMap().keySet();
        for (String varName : varNames) {
            SchemaVariable sv = insts.lookupVar(new Name(varName));
            Object value = insts.getInstantiation(sv);
            va.addAssignmentWithType(varName, value, assignments.getTypeMap().get(varName));
        }
        return va;

    }

    /**
     * Adds the variables of VariableAssignments to the namespace
     *
     * @param assignments VariabelAssignments containing variable names and types
     */
    private void buildNameSpace(VariableAssignments assignments, Services services) {
        String decalarations = buildDecls(assignments);
        parseDecls(decalarations, services);

    }

    /**
     * Builds a string that is used to create a new schemavariable declaration for the matchpattern
     *
     * @param assignments varaiables appearing as schema varaibels in the match pattern and their
     *        types (in KeY)
     * @return a String representing the declaration part of a taclet for teh matchpattern
     */
    private String buildDecls(VariableAssignments assignments) {
        Map<String, VariableAssignments.VarType> typeMap = assignments.getTypeMap();
        String schemaVars = "\\schemaVariables {\n";
        final List<String> strn = new ArrayList<>();

        typeMap.forEach((id, type) -> strn.add(toDecl(id, type)));
        schemaVars += String.join("\n", strn);
        schemaVars += "}";
        LOGGER.debug("Schema Variables: {}", schemaVars);
        return schemaVars;
    }

    private String toDecl(String id, VariableAssignments.VarType type) {
        return type.getKeYDeclarationPrefix() + " " + id + ";";
    }

    /**
     * Parse the declaration string for the current pattern and add the variables to the namespace
     *
     * @param s declaration part of a taclet
     */
    public void parseDecls(String s, Services services) {
        try {
            KeyIO io = new KeyIO(services);
            KeyAst.File ctx = ParsingFacade.parseFile(CharStreams.fromString(s));
            io.evalDeclarations(ctx);
        } catch (Exception e) {
            LOGGER.error("Exception while Parsing.", e);
        }
    }

    private Taclet parseTaclet(String s, Services services) {
        KeyIO io = new KeyIO(services);
        KeyAst.File ctx = ParsingFacade.parseFile(CharStreams.fromString(s));
        io.evalDeclarations(ctx);
        io.evalFuncAndPred(ctx);
        return io.findTaclets(ctx).get(0);
    }

}
