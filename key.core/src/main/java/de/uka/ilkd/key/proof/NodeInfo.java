/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import java.util.HashSet;
import java.util.Objects;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.logic.SequentChangeInfo;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.rule.AbstractAuxiliaryContractBuiltInRuleApp;
import de.uka.ilkd.key.rule.AbstractContractRuleApp;
import de.uka.ilkd.key.rule.LoopInvariantBuiltInRuleApp;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.TermInstantiation;

import org.key_project.util.collection.ImmutableList;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;


/**
 * The node info object contains additional information about a node used to give user feedback. The
 * content does not have any influence on the proof or carry something of logical value.
 */
public class NodeInfo {
    private static final Logger LOGGER = LoggerFactory.getLogger(NodeInfo.class);

    private static final Set<Name> symbolicExecNames = new HashSet<>(9);

    /** firstStatement stripped of method frames */
    private SourceElement activeStatement = null;

    private String branchLabel = null;

    /** flag true if the first and active statement have been determined */
    private boolean determinedFstAndActiveStatement = false;

    /** used for proof tree annotation when applicable */
    private SourceElement firstStatement = null;

    private String firstStatementString = null;

    /** the node this info object belongs to */
    private final Node node;

    /** has the rule app of the node been applied interactively? */
    private boolean interactiveApplication = false;

    /** has the rule app of the node been applied by a proof script? */
    private boolean scriptingApplication = false;

    /**
     * Has the rule app been determined as superfluous by some proof analysis algorithm?
     */
    private boolean uselessApplication = false;

    /** User-provided plain-text annotations to the node. */
    private String notes;

    /** Information about changes respective to the parent of this node. */
    private SequentChangeInfo sequentChangeInfo;

    public NodeInfo(Node node) {
        this.node = node;
    }

    static {
        symbolicExecNames.add(new Name("method_expand"));
        symbolicExecNames.add(new Name("simplify_prog"));
        symbolicExecNames.add(new Name("simplify_autoname"));
        symbolicExecNames.add(new Name("executeIntegerAssignment"));
        symbolicExecNames.add(new Name("simplify_object_creation"));
        symbolicExecNames.add(new Name("split_if"));
        symbolicExecNames.add(new Name("split_cond"));
        symbolicExecNames.add(new Name("simplify_expression"));
        symbolicExecNames.add(new Name("loop_expand"));
        symbolicExecNames.add(new Name("loop_scope_expand"));
        symbolicExecNames.add(new Name("loop_scope_inv_taclet"));
    }

    /**
     * Copy the NodeInfo of another proof node into this object.
     * Copies {@link #interactiveApplication}, {@link #scriptingApplication},
     * {@link #uselessApplication} and {@link #notes}.
     *
     * @param node a proof node
     */
    public void copyFrom(Node node) {
        interactiveApplication = node.getNodeInfo().interactiveApplication;
        scriptingApplication = node.getNodeInfo().scriptingApplication;
        uselessApplication = node.getNodeInfo().uselessApplication;
        notes = node.getNodeInfo().notes;
    }


    /**
     * determines the first and active statement if the applied taclet worked on a modality
     */
    private void determineFirstAndActiveStatement() {
        if (determinedFstAndActiveStatement) {
            return;
        }
        final RuleApp ruleApp = node.getAppliedRuleApp();
        if (ruleApp instanceof PosTacletApp) {
            firstStatement = computeFirstStatement(ruleApp);
            firstStatementString = null;
            activeStatement = computeActiveStatement(ruleApp);
            determinedFstAndActiveStatement = true;
        }
    }

    /**
     * <p>
     * Computes the active statement in the given {@link RuleApp}.
     * </p>
     * <p>
     * This functionality is independent from concrete {@link NodeInfo}s and used for instance by
     * the symbolic execution tree extraction.
     * </p>
     *
     * @param ruleApp The given {@link RuleApp}.
     * @return The active statement or {@code null} if no one is provided.
     */
    public static SourceElement computeActiveStatement(RuleApp ruleApp) {
        SourceElement firstStatement = computeFirstStatement(ruleApp);
        return computeActiveStatement(firstStatement);
    }

    /**
     * <p>
     * Computes the first statement in the given {@link RuleApp}.
     * </p>
     * <p>
     * This functionality is independent from concrete {@link NodeInfo}s and used for instance by
     * the symbolic execution tree extraction.
     * </p>
     *
     * @param ruleApp The given {@link RuleApp}.
     * @return The first statement or {@code null} if no one is provided.
     */
    public static SourceElement computeFirstStatement(RuleApp ruleApp) {
        SourceElement firstStatement = null;
        // TODO: unify with MiscTools getActiveStatement
        if (ruleApp instanceof PosTacletApp) {
            PosTacletApp pta = (PosTacletApp) ruleApp;
            if (!isSymbolicExecution(pta.taclet())) {
                return null;
            }
            Term t = TermBuilder.goBelowUpdates(pta.posInOccurrence().subTerm());
            final ProgramElement pe = t.javaBlock().program();
            if (pe != null) {
                firstStatement = pe.getFirstElement();
            }
        }
        return firstStatement;
    }

    /**
     * <p>
     * Computes the active statement in the given {@link SourceElement}.
     * </p>
     * <p>
     * This functionality is independent from concrete {@link NodeInfo}s and used for instance by
     * the symbolic execution tree extraction.
     * </p>
     *
     * @param firstStatement The given {@link SourceElement}.
     * @return The active statement or {@code null} if no one is provided.
     */
    public static SourceElement computeActiveStatement(SourceElement firstStatement) {
        SourceElement activeStatement = null;
        // TODO: unify with MiscTools getActiveStatement
        if (firstStatement != null) {
            activeStatement = firstStatement;
            while ((activeStatement instanceof ProgramPrefix)
                    && !(activeStatement instanceof StatementBlock)) {
                activeStatement = activeStatement.getFirstElement();
            }
        }
        return activeStatement;
    }

    void updateNoteInfo() {
        determinedFstAndActiveStatement = false;
        firstStatement = null;
        firstStatementString = null;
        activeStatement = null;
        determineFirstAndActiveStatement();
    }

    /**
     * Checks if a rule is applied on the given {@link Node} which performs symbolic execution.
     *
     * @param node The {@link Node} to check.
     * @return {@code true} symbolic execution is performed, {@code false} otherwise.
     */
    public static boolean isSymbolicExecutionRuleApplied(Node node) {
        if (node != null) {
            return isSymbolicExecutionRuleApplied(node.getAppliedRuleApp());
        } else {
            return false;
        }
    }

    /**
     * Checks if the given {@link RuleApp} performs symbolic execution.
     *
     * @param app The {@link RuleApp} to check.
     * @return {@code true} symbolic execution is performed, {@code false} otherwise.
     */
    public static boolean isSymbolicExecutionRuleApplied(RuleApp app) {
        return app instanceof AbstractAuxiliaryContractBuiltInRuleApp
                || app instanceof AbstractContractRuleApp
                || app instanceof LoopInvariantBuiltInRuleApp || app instanceof TacletApp
                        && NodeInfo.isSymbolicExecution(((TacletApp) app).taclet());
    }

    public static boolean isSymbolicExecution(Taclet t) {
        ImmutableList<RuleSet> list = t.getRuleSets();
        RuleSet rs;
        while (!list.isEmpty()) {
            rs = list.head();
            Name name = rs.name();
            if (symbolicExecNames.contains(name)) {
                return true;
            }
            list = list.tail();
        }
        return false;
    }

    /**
     * returns the active statement of the JavaBlock the applied rule has been matched against or
     * null if no rule has been applied yet or the applied rule was no taclet or program
     * transformation rule
     *
     * @return active statement as described above
     */
    public SourceElement getActiveStatement() {
        determineFirstAndActiveStatement();
        return activeStatement;
    }

    /**
     * returns the branch label
     *
     * @return branch label
     */
    public String getBranchLabel() {
        return branchLabel;
    }

    /**
     * returns the position of the executed statement in its source code or Position.UNDEFINED
     *
     * @return statement position as described above
     */
    public Position getExecStatementPosition() {
        determineFirstAndActiveStatement();
        return (activeStatement == null) ? Position.UNDEFINED : activeStatement.getStartPosition();
    }

    /**
     * returns a string representation of the first statement or null if no such exists
     *
     * @return string representation of first statement as described above
     */
    public String getFirstStatementString() {
        determineFirstAndActiveStatement();
        if (firstStatement != null) {
            if (firstStatementString == null) {
                firstStatementString = String.valueOf(firstStatement);
            }
            firstStatementString = String.valueOf(activeStatement);
            return firstStatementString;
        }
        return null;
    }

    /**
     * sets the branch label of a node. Schema variables occurring in string <tt>s</tt> are replaced
     * by their instantiations if possible
     *
     * @param s the String to be set
     */
    public void setBranchLabel(String s) {
        determineFirstAndActiveStatement();
        if (s == null) {
            return;
        }
        if (node.parent() == null) {
            return;
        }
        RuleApp ruleApp = node.parent().getAppliedRuleApp();
        if (ruleApp instanceof TacletApp) {
            TacletApp tacletApp = (TacletApp) ruleApp; // XXX

            Pattern p = Pattern.compile("#\\w+");
            Matcher m = p.matcher(s);
            StringBuffer sb = new StringBuffer();
            while (m.find()) {
                String arg = m.group();
                Object val = tacletApp.instantiations().lookupValue(new Name(arg));
                if (val == null) {
                    // chop off the leading '#'
                    String arg2 = arg.substring(1);
                    val = tacletApp.instantiations().lookupValue(new Name(arg2));
                }
                String res;
                if (val == null) {
                    LOGGER.warn(
                        "No instantiation for {}. Probably branch label not up to date in {}", arg,
                        tacletApp.rule().name());
                    res = arg; // use sv name instead
                } else {
                    if (val instanceof Term) {
                        val = TermLabel.removeIrrelevantLabels((Term) val,
                            node.proof().getServices());
                    } else if (val instanceof TermInstantiation) {
                        val = TermLabel.removeIrrelevantLabels(
                            ((TermInstantiation) val).getInstantiation(),
                            node.proof().getServices());
                    }
                    res = ProofSaver.printAnything(val, node.proof().getServices());
                }
                m.appendReplacement(sb, res.replace("$", "\\$"));
            }
            m.appendTail(sb);
            // eliminate annoying whitespaces
            Pattern whiteSpacePattern = Pattern.compile("\\s+");
            Matcher whiteSpaceMatcher = whiteSpacePattern.matcher(sb);
            branchLabel = whiteSpaceMatcher.replaceAll(" ");
        } else {
            branchLabel = s;
        }
    }

    /**
     * parameter indicated if the rule has been applied interactively or not
     *
     * @param b a boolean indicating interactive application
     */
    public void setInteractiveRuleApplication(boolean b) {
        interactiveApplication = b;
    }

    /**
     * parameter indicated if the rule has been applied by a proof script or not
     *
     * @param b a boolean indicating scripting application
     */
    public void setScriptRuleApplication(boolean b) {
        scriptingApplication = b;
    }

    /**
     * returns true if the rule applied on this node has been performed manually by the user
     *
     * @return boolean for interactive rule application as described above
     */
    public boolean getInteractiveRuleApplication() {
        return interactiveApplication;
    }

    /**
     * returns true if the rule applied on this node has been performed by a proof script command.
     * For rule, macro commands etc., the first node is marked.
     *
     * @return boolean for proof script rule application as described above
     */
    public boolean getScriptRuleApplication() {
        return scriptingApplication;
    }

    /**
     * Add user-provided plain-text annotations.
     *
     * @param newNotes annotations as described above
     */
    public void setNotes(String newNotes) {
        String oldNotes = notes;
        notes = newNotes;
        if (!Objects.equals(oldNotes, newNotes)) {
            node.proof().fireNotesChanged(node);
        }
    }

    /**
     * Get user-provided plain-text annotations.
     *
     * @return annotations as described above
     */
    public String getNotes() {
        return notes;
    }

    public SequentChangeInfo getSequentChangeInfo() {
        return sequentChangeInfo;
    }

    public void setSequentChangeInfo(SequentChangeInfo sequentChangeInfo) {
        this.sequentChangeInfo = sequentChangeInfo;
    }

    /**
     * @return whether the proof step does not contribute to the proof
     */
    public boolean isUselessApplication() {
        return uselessApplication;
    }

    /**
     * Mark this node as useless or useful.
     *
     * @param uselessApplication whether this node should be marked as useless
     */
    public void setUselessApplication(boolean uselessApplication) {
        this.uselessApplication = uselessApplication;
    }
}
