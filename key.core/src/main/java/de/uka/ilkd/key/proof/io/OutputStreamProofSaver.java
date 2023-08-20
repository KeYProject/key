/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.io;

import java.io.*;
import java.nio.charset.StandardCharsets;
import java.util.*;

import de.uka.ilkd.key.axiom_abstraction.AbstractDomainElement;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.AbstractionPredicate;
import de.uka.ilkd.key.informationflow.po.AbstractInfFlowPO;
import de.uka.ilkd.key.informationflow.po.InfFlowCompositePO;
import de.uka.ilkd.key.informationflow.proof.InfFlowProof;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.PrettyPrinter;
import de.uka.ilkd.key.proof.NameRecorder;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.IPersistablePO;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.IProofFileParser.ProofElementID;
import de.uka.ilkd.key.proof.mgt.RuleJustification;
import de.uka.ilkd.key.proof.mgt.RuleJustificationBySpec;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.inst.InstantiationEntry;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.inst.TermInstantiation;
import de.uka.ilkd.key.rule.merge.CloseAfterMergeRuleBuiltInRuleApp;
import de.uka.ilkd.key.rule.merge.MergeProcedure;
import de.uka.ilkd.key.rule.merge.MergeRuleBuiltInRuleApp;
import de.uka.ilkd.key.rule.merge.procedures.MergeWithLatticeAbstraction;
import de.uka.ilkd.key.rule.merge.procedures.MergeWithPredicateAbstraction;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.settings.StrategySettings;
import de.uka.ilkd.key.smt.SMTRuleApp;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.KeYConstants;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMapEntry;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Saves a proof to a given {@link OutputStream}.
 *
 * @author Kai Wallisch
 */
public class OutputStreamProofSaver {
    private static final Logger LOGGER = LoggerFactory.getLogger(OutputStreamProofSaver.class);

    /**
     * The proof to save.
     */
    protected final Proof proof;
    /**
     * Currently running KeY version (usually a git commit hash).
     */
    protected final String internalVersion;
    /**
     * Whether the proof steps should be output (usually true).
     */
    protected final boolean saveProofSteps;


    /**
     * Extracts java source directory from {@link Proof#header()}, if it exists.
     *
     * @param proof the Proof
     * @return the location of the java source code or null if no such exists
     */
    public static File getJavaSourceLocation(Proof proof) {
        final String header = proof.header();
        final int i = header.indexOf("\\javaSource");
        if (i >= 0) {
            final int begin = header.indexOf('\"', i);
            final int end = header.indexOf('\"', begin + 1);
            final String sourceLocation = header.substring(begin + 1, end);
            if (sourceLocation.length() > 0) {
                return new File(sourceLocation);
            }
        }
        return null;
    }

    public OutputStreamProofSaver(Proof proof) {
        this(proof, KeYConstants.INTERNAL_VERSION);
    }

    public OutputStreamProofSaver(Proof proof, String internalVersion) {
        this.proof = proof;
        this.internalVersion = internalVersion;
        this.saveProofSteps = true;
    }

    /**
     * Create a new OutputStreamProofSaver.
     *
     * @param proof the proof to save
     * @param internalVersion currently running KeY version
     * @param saveProofSteps whether to save the performed proof steps
     */
    public OutputStreamProofSaver(Proof proof, String internalVersion, boolean saveProofSteps) {
        this.proof = proof;
        this.internalVersion = internalVersion;
        this.saveProofSteps = saveProofSteps;
    }

    /**
     * Write users and KeY versions to buffer.
     *
     * @return a buffer containing user and KeY version.
     */
    public StringBuffer writeLog() {
        final StringBuffer logstr = new StringBuffer();
        // Advance the Log entries
        if (proof.userLog == null) {
            proof.userLog = new ArrayList<>();
        }
        if (proof.keyVersionLog == null) {
            proof.keyVersionLog = new ArrayList<>();
        }
        proof.userLog.add(System.getProperty("user.name"));
        proof.keyVersionLog.add(internalVersion);
        final int s = proof.userLog.size();
        for (int i = 0; i < s; i++) {
            logstr.append("(keyLog \"").append(i).append("\" (keyUser \"")
                    .append(proof.userLog.get(i)).append("\" ) (keyVersion \"")
                    .append(proof.keyVersionLog.get(i)).append("\"))\n");
        }
        return logstr;
    }

    public String writeProfile(Profile profile) {
        return "\\profile \"" + escapeCharacters(profile.name()) + "\";\n";
    }

    public String writeSettings(ProofSettings ps) {
        return "\\settings {\n\"" + escapeCharacters(ps.settingsToString()) + "\"\n}\n";
    }

    public void save(OutputStream out) throws IOException {
        proof.copyCachedGoals(null, null, null);
        try (var ps = new PrintWriter(out, true, StandardCharsets.UTF_8)) {
            final ProofOblInput po =
                proof.getServices().getSpecificationRepository().getProofOblInput(proof);
            LogicPrinter printer = createLogicPrinter(proof.getServices(), false);

            // profile
            ps.println(writeProfile(proof.getServices().getProfile()));

            // settings
            final StrategySettings strategySettings = proof.getSettings().getStrategySettings();
            final StrategyProperties strategyProperties =
                strategySettings.getActiveStrategyProperties();
            if (po instanceof AbstractInfFlowPO && (po instanceof InfFlowCompositePO
                    || !((InfFlowProof) proof).getIFSymbols().isFreshContract())) {
                strategyProperties.put(StrategyProperties.INF_FLOW_CHECK_PROPERTY,
                    StrategyProperties.INF_FLOW_CHECK_TRUE);
                strategySettings.setActiveStrategyProperties(strategyProperties);
                for (final SequentFormula s : proof.root().sequent().succedent().asList()) {
                    ((InfFlowProof) proof).addLabeledTotalTerm(s.formula());
                }
            } else {
                strategyProperties.put(StrategyProperties.INF_FLOW_CHECK_PROPERTY,
                    StrategyProperties.INF_FLOW_CHECK_FALSE);
                strategySettings.setActiveStrategyProperties(strategyProperties);
            }
            ps.println(writeSettings(proof.getSettings()));

            if (po instanceof AbstractInfFlowPO && (po instanceof InfFlowCompositePO
                    || !((InfFlowProof) proof).getIFSymbols().isFreshContract())) {
                strategyProperties.put(StrategyProperties.INF_FLOW_CHECK_PROPERTY,
                    StrategyProperties.INF_FLOW_CHECK_FALSE);
                strategySettings.setActiveStrategyProperties(strategyProperties);
            }

            // declarations of symbols, sorts
            String header = proof.header();
            header = makePathsRelative(header);
            ps.print(header);

            // \problem or \proofObligation
            if (po instanceof IPersistablePO
                    && (!(po instanceof AbstractInfFlowPO) || (!(po instanceof InfFlowCompositePO)
                            && ((InfFlowProof) proof).getIFSymbols().isFreshContract()))) {
                final Properties properties = new Properties();
                ((IPersistablePO) po).fillSaveProperties(properties);
                try (StringWriter writer = new StringWriter()) {
                    properties.store(writer, "Proof Obligation Settings");
                    ps.println(
                        "\\proofObligation \"" + escapeCharacters(writer.toString()) + "\";\n");
                }
            } else {
                if (po instanceof AbstractInfFlowPO && (po instanceof InfFlowCompositePO
                        || !((InfFlowProof) proof).getIFSymbols().isFreshContract())) {
                    final Properties properties = new Properties();
                    ((IPersistablePO) po).fillSaveProperties(properties);
                    ps.print(((InfFlowProof) proof).printIFSymbols());
                }
                final Sequent problemSeq = proof.root().sequent();
                ps.println("\\problem {");
                printer.printSemisequent(problemSeq.succedent());
                ps.println(printer.result());
                ps.println("}\n");
            }

            if (saveProofSteps) {
                // \proof
                ps.println("\\proof {");
                ps.println(writeLog());
                ps.println("(autoModeTime \"" + proof.getAutoModeTime() + "\")\n");
                node2Proof(proof.root(), ps);
                ps.println("}");
            }
        }
    }

    protected String getBasePath() throws IOException {
        File javaSourceLocation = getJavaSourceLocation(proof);
        if (javaSourceLocation != null) {
            return javaSourceLocation.getCanonicalPath();
        } else {
            return null;
        }
    }

    /**
     * Searches in the header for absolute paths to Java files and tries to replace them by paths
     * relative to the proof file to be saved.
     */
    private String makePathsRelative(String header) {
        final String[] search =
            new String[] { "\\javaSource", "\\bootclasspath", "\\classpath", "\\include" };
        final String basePath;
        String tmp = header;
        try {
            basePath = getBasePath();
            if (basePath == null) {
                // if \javaSource has not been set, do not modify paths.
                return header;
            }

            // locate filenames in header
            for (final String s : search) {
                int i = tmp.indexOf(s);
                if (i == -1) {
                    continue; // entry not in file
                }

                // put in everything before the keyword
                // bugfix #1138: changed i-1 to i
                String tmp2 = tmp.substring(0, i);
                StringBuilder relPathString = new StringBuilder();
                i += s.length();
                final int l = tmp.indexOf(';', i);

                // there may be more than one path
                while (0 <= tmp.indexOf('"', i) && tmp.indexOf('"', i) < l) {
                    if (relPathString.length() > 0) {
                        relPathString.append(", ");
                    }

                    // path is always put in quotation marks
                    final int k = tmp.indexOf('"', i) + 1;
                    final int j = tmp.indexOf('"', k);

                    // add new relative path
                    final String absPath = tmp.substring(k, j);
                    final String relPath = tryToMakeFilenameRelative(absPath, basePath);
                    final String correctedRelPath = relPath.equals("") ? "." : relPath;
                    relPathString.append(" \"").append(escapeCharacters(correctedRelPath))
                            .append("\"");
                    i = j + 1;
                }
                tmp2 = tmp2 + s + relPathString + ";";

                // put back in the rest
                tmp = tmp2 + (i < tmp.length() ? tmp.substring(l + 1) : "");
            }
        } catch (final IOException e) {
            LOGGER.warn("Failed to make relative", e);
        }
        return tmp;
    }

    /**
     * Try to create a relative path, but return the absolute path if a relative path cannot be
     * found. This may happen on Windows systems (bug #1480).
     */
    private static String tryToMakeFilenameRelative(String absPath, String basePath) {
        try {
            return MiscTools.makeFilenameRelative(absPath, basePath);
        } catch (final RuntimeException e) {
            return absPath;
        }
    }

    private String newNames2Proof(Node n) {
        StringBuilder s = new StringBuilder();
        final NameRecorder rec = n.getNameRecorder();
        if (rec == null) {
            return s.toString();
        }
        final ImmutableList<Name> proposals = rec.getProposals();
        if (proposals.isEmpty()) {
            return s.toString();
        }
        for (final Name proposal : proposals) {
            s.append(",").append(proposal);
        }
        return " (newnames \"" + s.substring(1) + "\")";
    }

    /**
     * Print applied taclet rule for a single taclet rule application into the passed writer.
     *
     * @param appliedRuleApp the rule application to be printed
     * @param prefix a string which the printed rule is concatenated to
     * @param output the writer in which the rule is printed
     * @throws IOException an exception thrown when printing fails
     */

    private void printSingleTacletApp(TacletApp appliedRuleApp, Node node, String prefix,
            Appendable output) throws IOException {

        output.append(prefix);
        output.append("(rule \"");
        output.append(appliedRuleApp.rule().name().toString());
        output.append("\"");
        output.append(posInOccurrence2Proof(node.sequent(), appliedRuleApp.posInOccurrence()));
        output.append(newNames2Proof(node));
        output.append(getInteresting(appliedRuleApp.instantiations()));
        final ImmutableList<IfFormulaInstantiation> l = appliedRuleApp.ifFormulaInstantiations();
        if (l != null) {
            output.append(ifFormulaInsts(node, l));
        }
        output.append("");
        userInteraction2Proof(node, output);
        notes2Proof(node, output);
        output.append(")\n");
    }

    /**
     * Print predicates for applied merge rule application into the passed writer.
     *
     * @param predAbstrRule the rule application with the predicates to be printed
     * @param output the writer in which the rule is printed
     * @throws IOException an exception thrown when printing fails
     */
    private void printPredicatesForSingleMergeRuleApp(MergeWithPredicateAbstraction predAbstrRule,
            Appendable output) throws IOException {
        output.append("(").append(ProofElementID.MERGE_ABSTRACTION_PREDICATES.getRawName())
                .append(" \"");
        boolean first = true;
        for (final Map.Entry<Sort, ArrayList<AbstractionPredicate>> predsForSorts : predAbstrRule
                .getPredicates().entrySet()) {
            for (final AbstractionPredicate pred : predsForSorts.getValue()) {
                if (first) {
                    first = false;

                } else {
                    output.append(", ");
                }
                output.append(pred.toParseableString(proof.getServices()));
            }
        }

        output.append("\")");

        output.append(" (")
                .append(ProofElementID.MERGE_PREDICATE_ABSTRACTION_LATTICE_TYPE.getRawName())
                .append("\"");
        output.append(predAbstrRule.getLatticeType().getName());

        output.append("\")");
    }

    /**
     * Print predicates for applied merge rule application into the passed writer.
     *
     * @param concreteRule the rule application with the abstract domain to be printed
     * @param output the writer in which the rule is printed
     * @throws IOException an exception thrown when printing fails
     */
    private void printLatticeAbstractionForSingleMergeRuleApp(
            MergeWithLatticeAbstraction concreteRule, Appendable output) throws IOException {
        final Map<ProgramVariable, AbstractDomainElement> userChoices =
            concreteRule.getUserChoices();

        if (!userChoices.isEmpty()) {
            output.append(" (").append(ProofElementID.MERGE_USER_CHOICES.getRawName())
                    .append(" \"");
            boolean first = true;
            for (var pair : userChoices.entrySet()) {
                final var key = pair.getKey();
                final var value = pair.getValue();
                if (first) {
                    first = false;
                } else {
                    output.append("`), ");

                }
                output.append(" ('").append(key.sort().toString()).append("").append(key.toString())
                        .append("', `").append(value.toParseableString(proof.getServices()))
                        .append("`), ");
            }

            output.append("\")");
        }
    }

    /**
     * Print applied merge rule for a single merge rule application into the passed writer.
     *
     * @param mergeApp the rule application to be printed
     * @param prefix a string which the printed rule is concatenated to
     * @param output the writer in which the rule is printed
     * @throws IOException an exception thrown when printing fails
     */
    private void printSingleMergeRuleApp(MergeRuleBuiltInRuleApp mergeApp, Node node, String prefix,
            Appendable output) throws IOException {
        final MergeProcedure concreteRule = mergeApp.getConcreteRule();

        output.append(" (").append(ProofElementID.MERGE_PROCEDURE.getRawName()).append(" \"");
        output.append(concreteRule.toString());
        output.append("\")");

        output.append(" (").append(ProofElementID.NUMBER_MERGE_PARTNERS.getRawName()).append(" \"");
        output.append(Integer.toString(mergeApp.getMergePartners().size()));
        output.append("\")");

        output.append(" (").append(ProofElementID.MERGE_ID.getRawName()).append(" \"");
        output.append(Integer.toString(mergeApp.getMergeNode().serialNr()));
        output.append("\")");

        if (mergeApp.getDistinguishingFormula() != null) {
            output.append(" (").append(ProofElementID.MERGE_DIST_FORMULA.getRawName())
                    .append(" \"");
            output.append(escapeCharacters(
                printAnything(mergeApp.getDistinguishingFormula(), proof.getServices(), false)
                        .trim().replaceAll("(\\r|\\n|\\r\\n)+", "")));
            output.append("\")");
        }

        // Predicates for merges with predicate abstraction.
        if (concreteRule instanceof MergeWithPredicateAbstraction
                && ((MergeWithPredicateAbstraction) concreteRule).getPredicates().size() > 0) {

            printPredicatesForSingleMergeRuleApp((MergeWithPredicateAbstraction) concreteRule,
                output);
        }

        if (concreteRule instanceof MergeWithLatticeAbstraction) {
            printLatticeAbstractionForSingleMergeRuleApp((MergeWithLatticeAbstraction) concreteRule,
                output);
        }
    }

    /*
     *
     * Print applied close-after-merge rule for a single close-after-merge rule application into the
     * passed writer.
     *
     * @param closeApp the rule application to be printed
     *
     * @param prefix a string which the printed rule is concatenated to
     *
     * @param output the writer in which the rule is printed
     *
     * @throws IOException an exception thrown when printing fails
     */
    private void printSingleCloseAfterMergeRuleApp(CloseAfterMergeRuleBuiltInRuleApp closeApp,
            Node node, String prefix, Appendable output) throws IOException {

        // TODO (DS): There may be problems here if the merge node is
        // pruned away. Need to test some cases and either check for
        // null pointers at this place or find a better solution.
        output.append(" (").append(ProofElementID.MERGE_NODE.getRawName()).append(" \"");
        output.append(Integer.toString(closeApp.getCorrespondingMergeNode().parent().serialNr()));
        output.append("\")");
    }

    private void printSingleSMTRuleApp(SMTRuleApp smtApp, Node node, String prefix,
            Appendable output) throws IOException {
        output.append(" (").append(ProofElementID.SOLVERTYPE.getRawName())
                .append(" \"").append(smtApp.getSuccessfulSolverName()).append("\")");
    }

    /**
     * Print rule justification for applied built-in rule application into the passed writer.
     *
     * @param appliedRuleApp the rule application to be printed
     * @param output the writer in which the rule is printed
     * @throws IOException an exception thrown when printing fails
     */
    private void printRuleJustification(IBuiltInRuleApp appliedRuleApp, Appendable output)
            throws IOException {
        final RuleJustification ruleJusti = proof.getInitConfig().getJustifInfo()
                .getJustification(appliedRuleApp, proof.getServices());

        assert ruleJusti instanceof RuleJustificationBySpec
                : "Please consult bug #1111 if this fails.";

        final RuleJustificationBySpec ruleJustiBySpec = (RuleJustificationBySpec) ruleJusti;
        output.append(" (contract \"");
        output.append(ruleJustiBySpec.getSpec().getName());
        output.append("\")");
    }

    /**
     * Print applied built-in rule for a single built-in rule application into the passed writer.
     *
     * @param appliedRuleApp the rule application to be printed
     * @param prefix a string which the printed rule is concatenated to
     * @param output the writer in which the rule is printed
     * @throws IOException an exception thrown when printing fails
     */
    private void printSingleBuiltInRuleApp(IBuiltInRuleApp appliedRuleApp, Node node, String prefix,
            Appendable output) throws IOException {
        output.append(prefix);
        output.append(" (builtin \"");
        output.append(appliedRuleApp.rule().name().toString());
        output.append("\"");
        output.append(posInOccurrence2Proof(node.sequent(), appliedRuleApp.posInOccurrence()));

        output.append(newNames2Proof(node));
        output.append(builtinRuleIfInsts(node, appliedRuleApp.ifInsts()));

        if (appliedRuleApp.rule() instanceof UseOperationContractRule
                || appliedRuleApp.rule() instanceof UseDependencyContractRule) {
            printRuleJustification(appliedRuleApp, output);

            // for operation contract rules we add the modality under which the rule was applied
            // -> needed for proof management tool
            if (appliedRuleApp.rule() instanceof UseOperationContractRule) {
                if (appliedRuleApp instanceof ContractRuleApp) {
                    ContractRuleApp app = (ContractRuleApp) appliedRuleApp;
                    Modality modality = (Modality) app.programTerm().op();
                    output.append(" (modality \"");
                    output.append(modality.toString());
                    output.append("\")");
                }
            }
        }
        if (appliedRuleApp instanceof MergeRuleBuiltInRuleApp) {
            printSingleMergeRuleApp((MergeRuleBuiltInRuleApp) appliedRuleApp, node, prefix, output);
        }

        if (appliedRuleApp instanceof CloseAfterMergeRuleBuiltInRuleApp) {
            printSingleCloseAfterMergeRuleApp((CloseAfterMergeRuleBuiltInRuleApp) appliedRuleApp,
                node, prefix, output);
        } else if (appliedRuleApp instanceof SMTRuleApp) {
            printSingleSMTRuleApp((SMTRuleApp) appliedRuleApp, node, prefix, output);
        }

        output.append("");
        userInteraction2Proof(node, output);
        notes2Proof(node, output);
        output.append(")\n");
    }

    /**
     * Print applied rule (s) for a single proof node into the passed writer.
     *
     * @param node the proof node to be printed
     * @param prefix a string which the printed rules are concatenated to
     * @param output the writer in which the rule(s) is /are printed
     * @throws IOException an exception thrown when printing fails
     */
    private void printSingleNode(Node node, String prefix, Appendable output) throws IOException {
        final RuleApp appliedRuleApp = node.getAppliedRuleApp();
        if (appliedRuleApp == null && (proof.getOpenGoal(node) != null)) {
            // open goal
            output.append(prefix);
            output.append(" (opengoal \"");
            final LogicPrinter printer = createLogicPrinter(proof.getServices(), false);

            printer.printSequent(node.sequent());
            output.append(escapeCharacters(printer.result().replace('\n', ' ')));
            output.append("\")\n");
            return;
        }

        if (appliedRuleApp instanceof TacletApp) {
            printSingleTacletApp((TacletApp) appliedRuleApp, node, prefix, output);
        } else if (appliedRuleApp instanceof IBuiltInRuleApp) {
            printSingleBuiltInRuleApp((IBuiltInRuleApp) appliedRuleApp, node, prefix, output);
        }
    }

    /**
     * Print applied rule(s) for a proof node and its decendants into the passed writer.
     *
     * @param node the proof node from which to be printed
     * @param prefix a string which the printed rules are concatenated to
     * @param output the writer in which the rule(s) is/are printed
     * @throws IOException an exception thrown when printing fails
     */
    private void collectProof(Node node, String prefix, Appendable output) throws IOException {

        printSingleNode(node, prefix, output);
        Iterator<Node> childrenIt;

        while (node.childrenCount() == 1) {
            childrenIt = node.childrenIterator();
            node = childrenIt.next();
            printSingleNode(node, prefix, output);
        }

        if (node.childrenCount() == 0) {
            return;
        }

        childrenIt = node.childrenIterator();

        while (childrenIt.hasNext()) {
            final Node child = childrenIt.next();
            output.append(prefix);
            final String branchLabel = child.getNodeInfo().getBranchLabel();

            // The branchLabel is ignored when reading in the proof,
            // print it if we have it, ignore it otherwise. (MU)
            if (branchLabel == null) {
                output.append("(branch\n");
            } else {
                output.append("(branch \"").append(escapeCharacters(branchLabel)).append("\"\n");
            }

            collectProof(child, prefix + "   ", output);
            output.append(prefix).append(")\n");
        }
    }

    /**
     * Check whether the applied rule of the passed proof node was performed interactively. If this
     * is the case, a user interaction label is appended.
     *
     * @param node the proof node to be checked
     * @param output the writer to which the label should be appended
     * @throws IOException an exception thrown in case printing fails
     */
    private void userInteraction2Proof(Node node, Appendable output) throws IOException {
        if (node.getNodeInfo().getInteractiveRuleApplication()) {
            output.append(" (userinteraction)");
        }
        if (node.getNodeInfo().getScriptRuleApplication()) {
            output.append(" (proofscript)");
        }
    }

    /**
     * Saves user provided notes to the proof if present.
     *
     * @param node the node to check for notes
     * @param output the writer to which to append the notes
     * @throws IOException if printing fails
     */
    private void notes2Proof(Node node, Appendable output) throws IOException {
        String notes = node.getNodeInfo().getNotes();
        if (notes != null) {
            output.append(" (notes \"");
            // to allow for quotes inside the notes: escape backslashes and quotes
            notes = notes.replace("\\\\", "\\\\\\\\");
            notes = notes.replace("\\\"", "\\\\\"");
            output.append(notes);
            output.append("\")");
        }
    }

    /**
     * Print applied rule(s) for a proof node and its decendants into the passed writer such that in
     * can be loaded again as a proof.
     *
     * @param node the proof node from which to be printed
     * @param ps the writer in which the rule(s) is/are printed
     * @throws IOException an exception thrown when printing fails
     */
    public void node2Proof(Node node, Appendable ps) throws IOException {
        ps.append("(branch \"dummy ID\"\n");
        collectProof(node, "", ps);
        ps.append(")\n");
    }

    public static String posInOccurrence2Proof(Sequent seq, PosInOccurrence pos) {
        if (pos == null) {
            return "";
        }
        return " (formula \"" + seq.formulaNumberInSequent(pos.isInAntec(), pos.sequentFormula())
            + "\")" + posInTerm2Proof(pos.posInTerm());
    }

    public static String posInTerm2Proof(PosInTerm pos) {
        if (pos == PosInTerm.getTopLevel()) {
            return "";
        }
        String s = " (term \"";
        final String list = pos.integerList(pos.reverseIterator()); // cheaper to read
        // in
        s = s + list.substring(1, list.length() - 1); // chop off "[" and "]"
        s = s + "\")";
        return s;
    }

    /**
     * Get the "interesting" instantiations of the provided object.
     *
     * @see SVInstantiations#interesting
     * @param inst instantiations
     * @return the "interesting" instantiations (serialized)
     */
    public Collection<String> getInterestingInstantiations(SVInstantiations inst) {
        Collection<String> s = new ArrayList<>();

        for (final ImmutableMapEntry<SchemaVariable, InstantiationEntry<?>> pair : inst
                .interesting()) {
            final SchemaVariable var = pair.key();

            final Object value = pair.value().getInstantiation();

            if (!(value instanceof Term || value instanceof ProgramElement
                    || value instanceof Name)) {
                throw new IllegalStateException("Saving failed.\n"
                    + "FIXME: Unhandled instantiation type: " + value.getClass());
            }

            String singleInstantiation =
                var.name() + "=" + printAnything(value, proof.getServices(), false);
            s.add(singleInstantiation);
        }

        return s;
    }

    private String getInteresting(SVInstantiations inst) {
        StringBuilder s = new StringBuilder();

        for (String singleInstantiation : getInterestingInstantiations(inst)) {
            s.append(" (inst \"").append(escapeCharacters(singleInstantiation)).append("\")");
        }

        return s.toString();
    }

    public String ifFormulaInsts(Node node, ImmutableList<IfFormulaInstantiation> l) {
        StringBuilder s = new StringBuilder();
        for (final IfFormulaInstantiation aL : l) {
            if (aL instanceof IfFormulaInstSeq) {
                final SequentFormula f = aL.getConstrainedFormula();
                s.append(" (ifseqformula \"")
                        .append(node.sequent()
                                .formulaNumberInSequent(((IfFormulaInstSeq) aL).inAntec(), f))
                        .append("\")");
            } else if (aL instanceof IfFormulaInstDirect) {

                final String directInstantiation =
                    printTerm(aL.getConstrainedFormula().formula(), node.proof().getServices());

                s.append(" (ifdirectformula \"").append(escapeCharacters(directInstantiation))
                        .append("\")");
            } else {
                throw new IllegalArgumentException("Unknown If-Seq-Formula type");
            }
        }

        return s.toString();
    }

    public String builtinRuleIfInsts(Node node, ImmutableList<PosInOccurrence> ifInsts) {
        StringBuilder s = new StringBuilder();
        for (final PosInOccurrence ifInst : ifInsts) {
            s.append(" (ifInst \"\" ");
            s.append(posInOccurrence2Proof(node.sequent(), ifInst));
            s.append(")");
        }
        return s.toString();
    }

    /**
     * double escapes quotation marks and backslashes to be storeable in a text file
     *
     * @param toEscape the String to double escape
     * @return the escaped version of the string
     */
    public static String escapeCharacters(String toEscape) {

        String result = toEscape;

        // first escape backslash
        result = result.replaceAll("\\\\", "\\\\\\\\");
        // then escape quotation marks
        result = result.replaceAll("\"", "\\\\\"");

        return result;
    }

    public static String printProgramElement(ProgramElement pe) {
        PrettyPrinter printer = PrettyPrinter.purePrinter();
        printer.printFragment(pe);
        return printer.result();
    }

    public static String printTerm(Term t, Services serv) {
        return printTerm(t, serv, false);
    }

    public static String printTerm(Term t, Services serv, boolean shortAttrNotation) {
        final LogicPrinter logicPrinter = createLogicPrinter(serv, shortAttrNotation);
        logicPrinter.printTerm(t);
        return logicPrinter.result();
    }

    public static String printAnything(Object val, Services services) {
        return printAnything(val, services, true);
    }

    public static String printAnything(Object val, Services services,
            boolean shortAttrNotation) {
        if (val instanceof ProgramElement) {
            return printProgramElement((ProgramElement) val);
        } else if (val instanceof Term) {
            return printTerm((Term) val, services, shortAttrNotation);
        } else if (val instanceof Sequent) {
            return printSequent((Sequent) val, services);
        } else if (val instanceof Name) {
            return val.toString();
        } else if (val instanceof TermInstantiation) {
            return printTerm(((TermInstantiation) val).getInstantiation(), services);
        } else if (val == null) {
            return null;
        } else {
            LOGGER.warn("Don't know how to prettyprint {}", val.getClass());
            // try to String by chance
            return val.toString();
        }
    }

    private static String printSequent(Sequent val, Services services) {
        final LogicPrinter printer = createLogicPrinter(services, services == null);
        printer.printSequent(val);
        return printer.result();
    }

    private static LogicPrinter createLogicPrinter(Services serv, boolean shortAttrNotation) {

        final NotationInfo ni = new NotationInfo();

        return LogicPrinter.purePrinter(ni, (shortAttrNotation ? serv : null));
    }

}
