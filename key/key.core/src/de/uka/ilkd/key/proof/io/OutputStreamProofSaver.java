// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof.io;

import java.io.File;
import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.Map;
import java.util.Properties;
import java.util.Vector;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMapEntry;

import de.uka.ilkd.key.axiom_abstraction.AbstractDomainElement;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.AbstractionPredicate;
import de.uka.ilkd.key.informationflow.po.AbstractInfFlowPO;
import de.uka.ilkd.key.informationflow.po.InfFlowCompositePO;
import de.uka.ilkd.key.informationflow.proof.InfFlowProof;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.NameRecorder;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.IPersistablePO;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.IProofFileParser.ProofElementID;
import de.uka.ilkd.key.proof.mgt.RuleJustification;
import de.uka.ilkd.key.proof.mgt.RuleJustificationBySpec;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.IfFormulaInstDirect;
import de.uka.ilkd.key.rule.IfFormulaInstSeq;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.UseDependencyContractRule;
import de.uka.ilkd.key.rule.UseOperationContractRule;
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
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.KeYConstants;
import de.uka.ilkd.key.util.MiscTools;

/**
 * Saves a proof to a given {@link OutputStream}.
 *
 * @author Kai Wallisch
 */
public class OutputStreamProofSaver {

    /**
     * Extracts java source directory from {@link Proof#header()}, if it exists.
     *
     * @param proof
     *            the Proof
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

    protected final Proof proof;
    protected final String internalVersion;

    LogicPrinter printer;

    public OutputStreamProofSaver(Proof proof) {
        this(proof, KeYConstants.INTERNAL_VERSION);
    }

    public OutputStreamProofSaver(Proof proof, String internalVersion) {
        this.proof = proof;
        this.internalVersion = internalVersion;
    }

    /**
     * Write the log information of the proof including the KeY version and the user name.
     * @return a string buffer containing the log information mentioned above
     */
    public StringBuffer writeLog() {
        final StringBuffer logstr = new StringBuffer();
        // Advance the Log entries
        if (proof.userLog == null) {
            proof.userLog = new Vector<String>();
        }
        if (proof.keyVersionLog == null) {
            proof.keyVersionLog = new Vector<String>();
        }
        proof.userLog.add(System.getProperty("user.name"));
        proof.keyVersionLog.add(internalVersion);
        final int s = proof.userLog.size();
        for (int i = 0; i < s; i++) {
            logstr.append("(keyLog \"" + i + "\" (keyUser \""
                    + proof.userLog.elementAt(i) + "\" ) (keyVersion \""
                    + proof.keyVersionLog.elementAt(i) + "\"))\n");
        }
        return logstr;
    }

    public String writeProfile(Profile profile) {
        return "\\profile \"" + escapeCharacters(profile.name()) + "\";\n";
    }

    public String writeSettings(ProofSettings ps) {
        return "\\settings {\n\"" + escapeCharacters(ps.settingsToString())
                + "\"\n}\n";
    }

    public void save(OutputStream out) throws IOException {
        PrintWriter ps = null;

        try {
            ps = new PrintWriter(out, true);
            final ProofOblInput po = proof.getServices()
                    .getSpecificationRepository().getProofOblInput(proof);
            printer = createLogicPrinter(proof.getServices(), false);

            // profile
            ps.println(writeProfile(proof.getServices().getProfile()));

            // settings
            final StrategySettings strategySettings = proof.getSettings()
                    .getStrategySettings();
            final StrategyProperties strategyProperties = strategySettings
                    .getActiveStrategyProperties();
            if (po instanceof AbstractInfFlowPO
                    && (po instanceof InfFlowCompositePO
                            || !((InfFlowProof) proof).getIFSymbols()
                                    .isFreshContract())) {
                strategyProperties.put(
                    StrategyProperties.INF_FLOW_CHECK_PROPERTY,
                    StrategyProperties.INF_FLOW_CHECK_TRUE);
                strategySettings
                        .setActiveStrategyProperties(strategyProperties);
                for (final SequentFormula s : proof.root().sequent().succedent()
                        .asList()) {
                    ((InfFlowProof) proof).addLabeledTotalTerm(s.formula());
                }
            } else {
                strategyProperties.put(
                    StrategyProperties.INF_FLOW_CHECK_PROPERTY,
                    StrategyProperties.INF_FLOW_CHECK_FALSE);
                strategySettings
                        .setActiveStrategyProperties(strategyProperties);
            }
            ps.println(writeSettings(proof.getSettings()));

            if (po instanceof AbstractInfFlowPO
                    && (po instanceof InfFlowCompositePO
                            || !((InfFlowProof) proof).getIFSymbols()
                                    .isFreshContract())) {
                strategyProperties.put(
                    StrategyProperties.INF_FLOW_CHECK_PROPERTY,
                    StrategyProperties.INF_FLOW_CHECK_FALSE);
                strategySettings
                        .setActiveStrategyProperties(strategyProperties);
            }

            // declarations of symbols, sorts
            String header = proof.header();
            header = makePathsRelative(header);
            ps.print(header);

            // \problem or \proofObligation
            if (po instanceof IPersistablePO
                    && (!(po instanceof AbstractInfFlowPO)
                            || (!(po instanceof InfFlowCompositePO)
                                    && ((InfFlowProof) proof).getIFSymbols()
                                            .isFreshContract()))) {
                final Properties properties = new Properties();
                ((IPersistablePO) po).fillSaveProperties(properties);
                final StringWriter writer = new StringWriter();
                try {
                    properties.store(writer, "Proof Obligation Settings");
                    ps.println("\\proofObligation \""
                            + escapeCharacters(writer.toString()) + "\";\n");
                } finally {
                    writer.close();
                }
            } else {
                if (po instanceof AbstractInfFlowPO
                        && (po instanceof InfFlowCompositePO
                                || !((InfFlowProof) proof).getIFSymbols()
                                        .isFreshContract())) {
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

            // \proof
            ps.println("\\proof {");
            ps.println(writeLog());
            ps.println("(autoModeTime \"" + proof.getAutoModeTime() + "\")\n");
            node2Proof(proof.root(), ps);
            ps.println("}");

        } finally {
            if (out != null) {
                out.close();
            }
            if (ps != null) {
                ps.flush();
                ps.close();
            }
        }
    }

    protected String getBasePath() throws IOException {
        return getJavaSourceLocation(proof).getCanonicalPath();
    }

    /**
     * Searches in the header for absolute paths to Java files and tries to
     * replace them by paths relative to the proof file to be saved.
     */
    private String makePathsRelative(String header) {
        final String[] search = new String[] { "\\javaSource",
            "\\bootclasspath", "\\classpath", "\\include" };
        final String basePath;
        String tmp = header;
        try {
            basePath = getBasePath();

            // locate filenames in header
            for (final String s : search) {
                int i = tmp.indexOf(s);
                if (i == -1) {
                    continue; // entry not in file
                }

                // put in everything before the keyword
                // bugfix #1138: changed i-1 to i
                String tmp2 = tmp.substring(0, i);
                String relPathString = "";
                i += s.length();
                final int l = tmp.indexOf(";", i);

                // there may be more than one path
                while (0 <= tmp.indexOf("\"", i) && tmp.indexOf("\"", i) < l) {
                    if (!relPathString.isEmpty()) {
                        relPathString += ", ";
                    }

                    // path is always put in quotation marks
                    final int k = tmp.indexOf("\"", i) + 1;
                    final int j = tmp.indexOf("\"", k);

                    // add new relative path
                    final String absPath = tmp.substring(k, j);
                    final String relPath = tryToMakeFilenameRelative(absPath,
                        basePath);
                    relPathString = relPathString + " \""
                            + escapeCharacters(relPath) + "\"";
                    i = j + 1;
                }
                tmp2 = tmp2 + s + relPathString + ";";

                // put back in the rest
                tmp = tmp2
                        + (i < tmp.length() ? tmp.substring(l + 1, tmp.length())
                                : "");
            }
        } catch (final IOException e) {
            e.printStackTrace();
        }
        return tmp;
    }

    /**
     * Try to create a relative path, but return the absolute path if a relative
     * path cannot be found. This may happen on Windows systems (bug #1480).
     */
    private static String tryToMakeFilenameRelative(String absPath,
            String basePath) {
        try {
            return MiscTools.makeFilenameRelative(absPath, basePath);
        } catch (final RuntimeException e) {
            return absPath;
        }
    }

    private String newNames2Proof(Node n) {
        String s = "";
        final NameRecorder rec = n.getNameRecorder();
        if (rec == null) {
            return s;
        }
        final ImmutableList<Name> proposals = rec.getProposals();
        if (proposals.isEmpty()) {
            return s;
        }
        for (final Name proposal : proposals) {
            s += "," + proposal;
        }
        return " (newnames \"" + s.substring(1) + "\")";
    }

    /**
     * Print applied taclet rule for a single taclet rule application into the passed writer.
     * @param appliedRuleApp            the rule application to be printed
     * @param prefix            a string which the printed rule is concatenated to
     * @param output            the writer in which the rule is printed
     * @throws IOException             an exception thrown when printing fails
     */

    private void printSingleTacletApp(TacletApp appliedRuleApp, Node node,
            String prefix, Appendable output) throws IOException {

        output.append(prefix);
        output.append("(rule \"");
        output.append(appliedRuleApp.rule().name().toString());
        output.append("\"");
        output.append(posInOccurrence2Proof(node.sequent(),
            appliedRuleApp.posInOccurrence()));
        output.append(newNames2Proof(node));
        output.append(getInteresting(appliedRuleApp.instantiations()));
        final ImmutableList<IfFormulaInstantiation> l = appliedRuleApp
                .ifFormulaInstantiations();
        if (l != null) {
            output.append(ifFormulaInsts(node, l));
        }
        output.append("");
        userInteraction2Proof(node, output);
        output.append(")\n");
    }

    /**
     * Print predicates for applied merge rule application into the passed writer.
     * @param predAbstrRule            the rule application with the predicates to be printed
     * @param output            the writer in which the rule is printed
     * @throws IOException             an exception thrown when printing fails
     */
    private void printPredicatesForSingleMergeRuleApp(
            MergeWithPredicateAbstraction predAbstrRule, Appendable output)
            throws IOException {
        output.append("(")
                .append(
                    ProofElementID.MERGE_ABSTRACTION_PREDICATES.getRawName())
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
                .append(ProofElementID.MERGE_PREDICATE_ABSTRACTION_LATTICE_TYPE
                        .getRawName())
                .append("\"");
        output.append(predAbstrRule.getLatticeType().getName());

        output.append("\")");
    }

    /**
     * Print predicates for applied merge rule application into the passed writer.
     * @param concreteRule            the rule application with the abstract domain to be printed
     * @param output            the writer in which the rule is printed
     * @throws IOException             an exception thrown when printing fails
     */
    private void printLatticeAbstractionForSingleMergeRuleApp(
            MergeWithLatticeAbstraction concreteRule, Appendable output)
            throws IOException {
        final Map<ProgramVariable, AbstractDomainElement> userChoices = concreteRule
                .getUserChoices();

        if (!userChoices.isEmpty()) {
            output.append(" (")
                    .append(ProofElementID.MERGE_USER_CHOICES.getRawName())
                    .append(" \"");
            boolean first = true;
            for (final ProgramVariable v : userChoices.keySet()) {
                if (first) {
                    first = false;
                } else {
                    output.append("`), ");

                }
                final AbstractDomainElement elem = userChoices.get(v);
                output.append(" ('").append(v.sort().toString()).append("")
                        .append(v.toString()).append("', `")
                        .append(elem.toParseableString(proof.getServices()))
                        .append("`), ");
            }

            output.append("\")");
        }
    }

    /**
     * Print applied merge rule for a single merge rule application into the passed writer.
     * @param mergeApp            the rule application to be printed
     * @param prefix            a string which the printed rule is concatenated to
     * @param output            the writer in which the rule is printed
     * @throws IOException             an exception thrown when printing fails
     */
    private void printSingleMergeRuleApp(MergeRuleBuiltInRuleApp mergeApp,
            Node node, String prefix, Appendable output) throws IOException {
        final MergeProcedure concreteRule = mergeApp.getConcreteRule();

        output.append(" (").append(ProofElementID.MERGE_PROCEDURE.getRawName())
                .append(" \"");
        output.append(concreteRule.toString());
        output.append("\")");

        output.append(" (")
                .append(ProofElementID.NUMBER_MERGE_PARTNERS.getRawName())
                .append(" \"");
        output.append(Integer.toString(mergeApp.getMergePartners().size()));
        output.append("\")");

        output.append(" (").append(ProofElementID.MERGE_ID.getRawName())
                .append(" \"");
        output.append(Integer.toString(mergeApp.getMergeNode().serialNr()));
        output.append("\")");

        if (mergeApp.getDistinguishingFormula() != null) {
            output.append(" (")
                    .append(ProofElementID.MERGE_DIST_FORMULA.getRawName())
                    .append(" \"");
            output.append(escapeCharacters(
                printAnything(mergeApp.getDistinguishingFormula(),
                    proof.getServices(), false).toString().trim()
                            .replaceAll("(\\r|\\n|\\r\\n)+", "")));
            output.append("\")");
        }

        // Predicates for merges with predicate abstraction.
        if (concreteRule instanceof MergeWithPredicateAbstraction
                && ((MergeWithPredicateAbstraction) concreteRule)
                        .getPredicates().size() > 0) {

            printPredicatesForSingleMergeRuleApp(
                (MergeWithPredicateAbstraction) concreteRule, output);
        }

        if (concreteRule instanceof MergeWithLatticeAbstraction) {
            printLatticeAbstractionForSingleMergeRuleApp(
                (MergeWithLatticeAbstraction) concreteRule, output);
        }
    }

    /*
     *
     * Print applied close-after-merge rule for a single close-after-merge rule application
     * into the passed writer.
     * @param closeApp            the rule application to be printed
     * @param prefix            a string which the printed rule is concatenated to
     * @param output            the writer in which the rule is printed
     * @throws IOException             an exception thrown when printing fails
     */
    private void printSingleCloseAfterMergeRuleApp(
            CloseAfterMergeRuleBuiltInRuleApp closeApp, Node node,
            String prefix, Appendable output) throws IOException {

        // TODO (DS): There may be problems here if the merge node is
        // pruned away. Need to test some cases and either check for
        // null pointers at this place or find a better solution.
        output.append(" (").append(ProofElementID.MERGE_NODE.getRawName())
                .append(" \"");
        output.append(Integer.toString(
            closeApp.getCorrespondingMergeNode().parent().serialNr()));
        output.append("\")");
    }

    /**
     * Print rule justification for applied built-in rule application into the passed writer.
     * @param appliedRuleApp            the rule application to be printed
     * @param output            the writer in which the rule is printed
     * @throws IOException             an exception thrown when printing fails
     */
    private void printRuleJustification(IBuiltInRuleApp appliedRuleApp,
            Appendable output) throws IOException {
        final RuleJustification ruleJusti = proof.getInitConfig()
                .getJustifInfo()
                .getJustification(appliedRuleApp, proof.getServices());

        assert ruleJusti instanceof RuleJustificationBySpec : "Please consult bug #1111 if this fails.";

        final RuleJustificationBySpec ruleJustiBySpec = (RuleJustificationBySpec) ruleJusti;
        output.append(" (contract \"");
        output.append(ruleJustiBySpec.getSpec().getName());
        output.append("\")");
    }

    /**
     * Print applied built-in rule for a single built-in rule application into the passed writer.
     * @param appliedRuleApp            the rule application to be printed
     * @param prefix            a string which the printed rule is concatenated to
     * @param output            the writer in which the rule is printed
     * @throws IOException             an exception thrown when printing fails
     */
    private void printSingleBuiltInRuleApp(IBuiltInRuleApp appliedRuleApp,
            Node node, String prefix, Appendable output) throws IOException {
        output.append(prefix);
        output.append(" (builtin \"");
        output.append(appliedRuleApp.rule().name().toString());
        output.append("\"");
        output.append(posInOccurrence2Proof(node.sequent(),
            appliedRuleApp.posInOccurrence()));

        output.append(newNames2Proof(node));
        output.append(builtinRuleIfInsts(node, appliedRuleApp.ifInsts()));

        if (appliedRuleApp.rule() instanceof UseOperationContractRule
                || appliedRuleApp.rule() instanceof UseDependencyContractRule) {
            printRuleJustification(appliedRuleApp, output);
        }
        if (appliedRuleApp instanceof MergeRuleBuiltInRuleApp) {
            printSingleMergeRuleApp((MergeRuleBuiltInRuleApp) appliedRuleApp,
                node, prefix, output);
        }

        if (appliedRuleApp instanceof CloseAfterMergeRuleBuiltInRuleApp) {
            printSingleCloseAfterMergeRuleApp(
                (CloseAfterMergeRuleBuiltInRuleApp) appliedRuleApp, node,
                prefix, output);
        }

        output.append("");
        userInteraction2Proof(node, output);

        output.append(")\n");
    }

    /**
     * Print applied rule (s) for a single proof node into the passed writer.
     * @param node            the proof node to be printed
     * @param prefix            a string which the printed rules are concatenated to
     * @param output            the writer in which the rule(s) is /are printed
     * @throws IOException             an exception thrown when printing fails
     */
    private void printSingleNode(Node node, String prefix, Appendable output)
            throws IOException {
        final RuleApp appliedRuleApp = node.getAppliedRuleApp();
        if (appliedRuleApp == null && (proof.getGoal(node) != null)) {
            // open goal
            output.append(prefix);
            output.append(" (opengoal \"");
            final LogicPrinter logicPrinter = createLogicPrinter(
                proof.getServices(), false);

            logicPrinter.printSequent(node.sequent());
            output.append(escapeCharacters(
                printer.result().toString().replace('\n', ' ')));
            output.append("\")\n");
            return;
        }

        if (appliedRuleApp instanceof TacletApp) {
            printSingleTacletApp((TacletApp) appliedRuleApp, node, prefix,
                output);
        }

        if (appliedRuleApp instanceof IBuiltInRuleApp) {
            printSingleBuiltInRuleApp((IBuiltInRuleApp) appliedRuleApp, node,
                prefix, output);
        }
    }

    /**
     * Print applied rule(s) for a proof node and its decendants into the passed writer.
     * @param node            the proof node from which to be printed
     * @param prefix            a string which the printed rules are concatenated to
     * @param output            the writer in which the rule(s) is/are printed
     * @throws IOException             an exception thrown when printing fails
     */
    private void collectProof(Node node, String prefix, Appendable output)
            throws IOException {

        printSingleNode(node, prefix, output);
        Iterator<Node> childrenIt = null;

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
                output.append(
                    "(branch \"" + escapeCharacters(branchLabel) + "\"\n");
            }

            collectProof(child, prefix + "   ", output);
            output.append(prefix + ")\n");
        }
    }

    /**
     * Check whether the applied rule of the passed proof node was performed interactively.
     * If this is the case, a user interaction label is appended.
     * @param node            the proof node to be checked
     * @param output            the writer to which the label is appended
     * @throws IOException             an exception thrown when printing fails
     */
    private void userInteraction2Proof(Node node, Appendable output)
            throws IOException {
        if (node.getNodeInfo().getInteractiveRuleApplication()) {
            output.append(" (userinteraction)");
        }
        if (node.getNodeInfo().getScriptRuleApplication()) {
            output.append(" (proofscript)");
        }
    }

    /**
     * Print applied rule(s) for a proof node and its decendants into the passed writer
     * such that in can be loaded again as a proof.
     * @param node            the proof node from which to be printed
     * @param ps            the writer in which the rule(s) is/are printed
     * @throws IOException             an exception thrown when printing fails
     */
    public void node2Proof(Node node, Appendable ps) throws IOException {
        ps.append("(branch \"dummy ID\"\n");
        collectProof(node, "", ps);
        ps.append(")\n");
    }

    public static String posInOccurrence2Proof(Sequent seq,
            PosInOccurrence pos) {
        if (pos == null) {
            return "";
        }
        return " (formula \""
                + seq.formulaNumberInSequent(pos.isInAntec(),
                    pos.sequentFormula())
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

    public String getInteresting(SVInstantiations inst) {
        // System.err.println(inst);
        String s = "";

        for (final ImmutableMapEntry<SchemaVariable, InstantiationEntry<?>> pair : inst
                .interesting()) {
            final SchemaVariable var = pair.key();

            final Object value = pair.value().getInstantiation();

            if (!(value instanceof Term || value instanceof ProgramElement
                    || value instanceof Name)) {
                throw new RuntimeException(
                    "Saving failed.\n" + "FIXME: Unhandled instantiation type: "
                            + value.getClass());
            }

            final StringBuffer singleInstantiation = new StringBuffer(
                var.name().toString()).append("=").append(
                    printAnything(value, proof.getServices(), false));

            s += " (inst \"" + escapeCharacters(singleInstantiation.toString())
                    + "\")";
        }

        return s;
    }

    public String ifFormulaInsts(Node node,
            ImmutableList<IfFormulaInstantiation> l) {
        String s = "";
        for (final IfFormulaInstantiation aL : l) {
            final IfFormulaInstantiation iff = aL;
            if (iff instanceof IfFormulaInstSeq) {
                final SequentFormula f = iff.getConstrainedFormula();
                s += " (ifseqformula \""
                        + node.sequent().formulaNumberInSequent(
                            ((IfFormulaInstSeq) iff).inAntec(), f)
                        + "\")";
            } else if (iff instanceof IfFormulaInstDirect) {

                final String directInstantiation = printTerm(
                    iff.getConstrainedFormula().formula(),
                    node.proof().getServices()).toString();

                s += " (ifdirectformula \""
                        + escapeCharacters(directInstantiation) + "\")";
            } else {
                throw new RuntimeException("Unknown If-Seq-Formula type");
            }
        }

        return s;
    }

    public String builtinRuleIfInsts(Node node,
            ImmutableList<PosInOccurrence> ifInsts) {
        String s = "";
        for (final PosInOccurrence ifInst : ifInsts) {
            s += " (ifInst \"\" ";
            s += posInOccurrence2Proof(node.sequent(), ifInst);
            s += ")";
        }
        return s;
    }

    /**
     * double escapes quotation marks and backslashes to be storeable in a text
     * file
     *
     * @param toEscape
     *            the String to double escape
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

    public static StringBuffer printProgramElement(ProgramElement pe) {
        final java.io.StringWriter sw = new java.io.StringWriter();
        final ProgramPrinter prgPrinter = new ProgramPrinter(sw);
        try {
            pe.prettyPrint(prgPrinter);
        } catch (final IOException ioe) {
            System.err.println(ioe);
        }
        return sw.getBuffer();
    }

    public static StringBuffer printTerm(Term t, Services serv) {
        return printTerm(t, serv, false);
    }

    public static StringBuffer printTerm(Term t, Services serv,
            boolean shortAttrNotation) {
        StringBuffer result;
        final LogicPrinter logicPrinter = createLogicPrinter(serv,
            shortAttrNotation);
        try {
            logicPrinter.printTerm(t);
        } catch (final IOException ioe) {
            System.err.println(ioe);
        }
        result = logicPrinter.result();
        if (result.charAt(result.length() - 1) == '\n') {
            result.deleteCharAt(result.length() - 1);
        }
        return result;
    }

    public static String printAnything(Object val, Services services) {
        return printAnything(val, services, true).toString();
    }

    public static StringBuffer printAnything(Object val, Services services,
            boolean shortAttrNotation) {
        if (val instanceof ProgramElement) {
            return printProgramElement((ProgramElement) val);
        } else if (val instanceof Term) {
            return printTerm((Term) val, services, shortAttrNotation);
        } else if (val instanceof Sequent) {
            return printSequent((Sequent) val, services);
        } else if (val instanceof Name) {
            return new StringBuffer(val.toString());
        } else if (val instanceof TermInstantiation) {
            return printTerm(((TermInstantiation) val).getInstantiation(),
                services);
        } else if (val == null) {
            return null;
        } else {
            System.err
                    .println("Don't know how to prettyprint " + val.getClass());
            // try to String by chance
            return new StringBuffer(val.toString());
        }
    }

    private static StringBuffer printSequent(Sequent val, Services services) {
        final LogicPrinter printer = createLogicPrinter(services,
            services == null);
        printer.printSequent(val);
        return printer.result();
    }

    private static LogicPrinter createLogicPrinter(Services serv,
            boolean shortAttrNotation) {

        final NotationInfo ni = new NotationInfo();
        LogicPrinter p = null;

        p = new LogicPrinter(new ProgramPrinter(null), ni,
            (shortAttrNotation ? serv : null), true);
        return p;
    }

}
