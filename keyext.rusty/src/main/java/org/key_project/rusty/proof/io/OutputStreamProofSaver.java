/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof.io;

import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintWriter;
import java.nio.charset.StandardCharsets;
import java.util.Iterator;

import org.key_project.logic.Name;
import org.key_project.logic.PosInTerm;
import org.key_project.logic.Term;
import org.key_project.prover.rules.AssumesFormulaInstantiation;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.logic.Sequent;
import org.key_project.rusty.logic.SequentFormula;
import org.key_project.rusty.pp.LogicPrinter;
import org.key_project.rusty.pp.NotationInfo;
import org.key_project.rusty.pp.PrettyPrinter;
import org.key_project.rusty.proof.Node;
import org.key_project.rusty.proof.Proof;
import org.key_project.rusty.proof.init.Profile;
import org.key_project.rusty.rule.AssumesFormulaInstSeq;
import org.key_project.rusty.rule.RuleApp;
import org.key_project.rusty.rule.TacletApp;
import org.key_project.rusty.rule.inst.TermInstantiation;
import org.key_project.rusty.settings.ProofSettings;
import org.key_project.util.collection.ImmutableList;

/**
 * Saves a proof to a given {@link OutputStream}.
 */
public class OutputStreamProofSaver {
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

    public OutputStreamProofSaver(Proof proof) {
        this(proof, "2.12.3 (Rusty)");
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

    public String writeProfile(Profile profile) {
        return "\\profile \"" + escapeCharacters(profile.name()) + "\";\n";
    }

    public String writeSettings(ProofSettings ps) {
        return ""; // String.format("\\settings %s \n", ps.settingsToString());
    }

    public void save(OutputStream out) throws IOException {
        try (var ps = new PrintWriter(out, true, StandardCharsets.UTF_8)) {
            // final ProofOblInput po =
            // proof.getServices().getSpecificationRepository().getProofOblInput(proof);
            LogicPrinter printer = createLogicPrinter(proof.getServices(), false);

            // profile
            ps.println(writeProfile(proof.getServices().getProfile()));

            // settings
            /*
             * final StrategySettings strategySettings = proof.getSettings().getStrategySettings();
             * final StrategyProperties strategyProperties =
             * strategySettings.getActiveStrategyProperties();
             * if (po instanceof AbstractInfFlowPO && (po instanceof InfFlowCompositePO
             * || !((InfFlowProof) proof).getIFSymbols().isFreshContract())) {
             * strategyProperties.put(StrategyProperties.INF_FLOW_CHECK_PROPERTY,
             * StrategyProperties.INF_FLOW_CHECK_TRUE);
             * strategySettings.setActiveStrategyProperties(strategyProperties);
             * for (final SequentFormula s : proof.root().sequent().succedent().asList()) {
             * ((InfFlowProof) proof).addLabeledTotalTerm(s.formula());
             * }
             * } else {
             * strategyProperties.put(StrategyProperties.INF_FLOW_CHECK_PROPERTY,
             * StrategyProperties.INF_FLOW_CHECK_FALSE);
             * strategySettings.setActiveStrategyProperties(strategyProperties);
             * }
             * ps.println(writeSettings(proof.getSettings()));
             *
             * if (po instanceof AbstractInfFlowPO && (po instanceof InfFlowCompositePO
             * || !((InfFlowProof) proof).getIFSymbols().isFreshContract())) {
             * strategyProperties.put(StrategyProperties.INF_FLOW_CHECK_PROPERTY,
             * StrategyProperties.INF_FLOW_CHECK_FALSE);
             * strategySettings.setActiveStrategyProperties(strategyProperties);
             * }
             */

            // declarations of symbols, sorts
            String header = proof.header();
            // header = makePathsRelative(header);
            ps.print(header);

            // \problem or \proofObligation
            /*
             * if (po instanceof IPersistablePO ppo
             * && (!(po instanceof AbstractInfFlowPO) || (!(po instanceof InfFlowCompositePO)
             * && ((InfFlowProof) proof).getIFSymbols().isFreshContract()))) {
             * var loadingConfig = ppo.createLoaderConfig();
             * ps.println("\\proofObligation ");
             * loadingConfig.save(ps, "Proof-Obligation settings");
             * ps.println("\n");
             * } else {
             * if (po instanceof AbstractInfFlowPO && (po instanceof InfFlowCompositePO
             * || !((InfFlowProof) proof).getIFSymbols().isFreshContract())) {
             * ps.print(((InfFlowProof) proof).printIFSymbols());
             * }
             */
            final Sequent problemSeq = proof.root().sequent();
            ps.println("\\problem {");
            if (problemSeq.antecedent().isEmpty() && problemSeq.succedent().size() == 1) {
                // Problem statement is a single formula ...
                printer.printSemisequent(problemSeq.succedent());
            } else {
                // Problem statement is a proper sequent ...
                printer.printSequent(problemSeq);
            }
            ps.println(printer.result());
            ps.println("}\n");
            // }

            if (saveProofSteps) {
                // \proof
                ps.println("\\proof {");
                // ps.println(writeLog());
                // ps.println("(autoModeTime \"" + proof.getAutoModeTime() + "\")\n");
                node2Proof(proof.root(), ps);
                ps.println("}");
            }
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

    private String newNames2Proof(Node n) {
        // TODO: What is this even used for?!
        /*
         * StringBuilder s = new StringBuilder();
         * final NameRecorder rec = n.getNameRecorder();
         * if (rec == null) {
         * return s.toString();
         * }
         * final ImmutableList<Name> proposals = rec.getProposals();
         * if (proposals.isEmpty()) {
         * return s.toString();
         * }
         * for (final Name proposal : proposals) {
         * s.append(",").append(proposal);
         * }
         * return " (newnames \"" + s.substring(1) + "\")";
         */
        return "";
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
        // TODO: output.append(getInteresting(appliedRuleApp.instantiations()));
        final ImmutableList<AssumesFormulaInstantiation> l =
            appliedRuleApp.assumesFormulaInstantiations();
        if (l != null) {
            output.append(ifFormulaInsts(node, l));
        }
        output.append("");
        // userInteraction2Proof(node, output);
        // notes2Proof(node, output);
        output.append(")\n");
    }

    public String ifFormulaInsts(Node node, ImmutableList<AssumesFormulaInstantiation> l) {
        StringBuilder s = new StringBuilder();
        for (final AssumesFormulaInstantiation aL : l) {
            if (aL instanceof AssumesFormulaInstSeq ifis) {
                final SequentFormula f = (SequentFormula) aL.getSequentFormula();
                s.append(" (ifseqformula \"")
                        .append(node.sequent()
                                .formulaNumberInSequent(ifis.inAntec(), f))
                        .append("\")");
            } /*
               * else if (aL instanceof IfFormulaInstDirect) {
               * final String directInstantiation =
               * printTerm(aL.getConstrainedFormula().formula(), node.proof().getServices());
               *
               * s.append(" (ifdirectformula \"").append(escapeCharacters(directInstantiation))
               * .append("\")");
               * }
               */ else {
                throw new IllegalArgumentException("Unknown If-Seq-Formula type");
            }
        }

        return s.toString();
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
        } /*
           * else if (appliedRuleApp instanceof IBuiltInRuleApp) {
           * printSingleBuiltInRuleApp((IBuiltInRuleApp) appliedRuleApp, node, prefix, output);
           * }
           */
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
            final String branchLabel = null;// child.getNodeInfo().getBranchLabel();

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

    public static String posInOccurrence2Proof(Sequent seq, PosInOccurrence pos) {
        if (pos == null) {
            return "";
        }
        return " (formula \""
            + seq.formulaNumberInSequent(pos.isInAntec(), pos.sequentFormula())
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

    public static String printProgramElement(RustyProgramElement pe) {
        PrettyPrinter printer = PrettyPrinter.purePrinter();
        printer.printFragment(pe);
        return printer.result();
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
        if (val instanceof RustyProgramElement pe) {
            return printProgramElement(pe);
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
            // LOGGER.warn("Don't know how to prettyprint {}", val.getClass());
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
