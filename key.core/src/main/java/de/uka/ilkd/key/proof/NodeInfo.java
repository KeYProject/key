/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import java.util.HashSet;
import java.util.Objects;
import java.util.Set;
import java.util.function.Supplier;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.SourceElement;
import de.uka.ilkd.key.java.ast.StatementBlock;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.rule.AbstractAuxiliaryContractBuiltInRuleApp;
import de.uka.ilkd.key.rule.AbstractContractRuleApp;
import de.uka.ilkd.key.rule.LoopInvariantBuiltInRuleApp;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;

import org.key_project.logic.Name;
import org.key_project.proof.LocationVariableTracker;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.rules.RuleSet;
import org.key_project.prover.sequent.SequentChangeInfo;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.parsing.Position;

import org.jspecify.annotations.Nullable;
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

    /** Materialised (resolved) branch label; computed lazily from the raw label / supplier. */
    private @Nullable String branchLabel = null;
    /** Raw taclet-template label whose {@code #sv} placeholders are substituted lazily. */
    private @Nullable String rawBranchLabel = null;
    /**
     * Lazy source for labels that stringify terms; evaluated on first {@link #getBranchLabel()}.
     */
    private @Nullable Supplier<String> branchLabelSupplier = null;
    /** Whether {@link #branchLabel} has already been resolved from the raw label / supplier. */
    private boolean branchLabelResolved = false;

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
     * Determines the first and active statement if the applied taclet worked on a modality.
     *
     * <p>
     * Computed lazily on demand and cached. The first/active statement is a <em>display</em>
     * concern
     * (GUI, proof-reference and symbolic-execution analyses); it is intentionally not needed for,
     * and
     * not computed during, proof search &mdash; see {@link #updateNoteInfo()}. {@code synchronized}
     * because the lazy computation mutates the cache fields and may be triggered concurrently after
     * a
     * (parallel) run, e.g. by the GUI. The pure, stateless variants
     * {@link #computeActiveStatement(RuleApp)} / {@link #computeFirstStatement(RuleApp)} derive the
     * same information from a rule app alone and are the thread-safe choice for any proving-time
     * use.
     */
    private synchronized void determineFirstAndActiveStatement() {
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
    public static SourceElement computeActiveStatement(
            RuleApp ruleApp) {
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
    public static SourceElement computeFirstStatement(
            RuleApp ruleApp) {
        SourceElement firstStatement = null;
        // TODO: unify with MiscTools getActiveStatement
        if (ruleApp instanceof PosTacletApp pta) {
            if (!isSymbolicExecution(pta.taclet())) {
                return null;
            }
            JTerm t = TermBuilder.goBelowUpdates((JTerm) pta.posInOccurrence().subTerm());
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

    synchronized void updateNoteInfo() {
        // Only invalidate the cached first/active statement; do NOT recompute eagerly.
        // Recomputation
        // happens lazily on demand (display / post-run analyses). Computing it here would (a) pull
        // this display computation onto the proof-search path -- a thread-safety hazard for the
        // parallel prover, NodeInfo must not be used for proving -- and (b) be wrong anyway, since
        // this runs from Node#setAppliedRuleApp *before* the new applied rule app is stored, so an
        // eager compute would use the stale (previous) rule app.
        determinedFstAndActiveStatement = false;
        firstStatement = null;
        firstStatementString = null;
        activeStatement = null;
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
                        && isSymbolicExecution(((TacletApp) app).taclet());
    }

    public static boolean isSymbolicExecution(Taclet t) {
        ImmutableList<RuleSet> list = t.getRuleSets();
        RuleSet rs;
        while (!list.isEmpty()) {
            rs = list.head();
            if (symbolicExecNames.contains(rs.name())) {
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
    public synchronized SourceElement getActiveStatement() {
        determineFirstAndActiveStatement();
        return activeStatement;
    }

    /**
     * returns the branch label
     *
     * @return branch label
     */
    public @Nullable synchronized String getBranchLabel() {
        if (!branchLabelResolved) {
            branchLabel = resolveBranchLabel(
                branchLabelSupplier != null ? branchLabelSupplier.get() : rawBranchLabel);
            branchLabelResolved = true;
        }
        return branchLabel;
    }

    /**
     * returns the position of the executed statement in its source code or Position.UNDEFINED
     *
     * @return statement position as described above
     */
    public synchronized Position getExecStatementPosition() {
        determineFirstAndActiveStatement();
        return (activeStatement == null) ? Position.UNDEFINED : activeStatement.getStartPosition();
    }

    /**
     * returns a string representation of the first statement or null if no such exists
     *
     * @return string representation of first statement as described above
     */
    public synchronized String getFirstStatementString() {
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
    public synchronized void setBranchLabel(String s) {
        // Store only the raw label; the #sv substitution / term pretty-printing below is deferred
        // to
        // getBranchLabel() (display/save). setBranchLabel is called during rule application for
        // named
        // branches, and nothing on the proof-search path reads the label, so doing that work here
        // was
        // wasteful and a thread-safety hazard for the parallel prover.
        if (s == null) {
            return;
        }
        rawBranchLabel = s;
        branchLabelSupplier = null;
        branchLabel = null;
        branchLabelResolved = false;
    }

    /**
     * Lazy variant of {@link #setBranchLabel(String)} for labels that stringify terms: the supplier
     * is evaluated (and its result substituted) only when {@link #getBranchLabel()} is first
     * called,
     * i.e. on display/save, never on the proof-search path.
     *
     * @param labelSupplier supplies the raw branch label on demand
     */
    public synchronized void setBranchLabel(Supplier<String> labelSupplier) {
        if (labelSupplier == null) {
            return;
        }
        branchLabelSupplier = labelSupplier;
        rawBranchLabel = null;
        branchLabel = null;
        branchLabelResolved = false;
    }

    /**
     * Resolves a raw branch label: schema variables occurring as {@code #sv} are replaced by their
     * (pretty-printed) instantiations if the parent rule is a taclet application. Runs lazily from
     * {@link #getBranchLabel()}, never on the proof-search path.
     *
     * @param s the raw label, or {@code null}
     * @return the resolved label, or {@code null}
     */
    private @Nullable String resolveBranchLabel(@Nullable String s) {
        if (s == null || node.parent() == null) {
            return null;
        }
        RuleApp ruleApp = node.parent().getAppliedRuleApp();
        if (ruleApp instanceof TacletApp tacletApp) {
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
                    if (val instanceof JTerm) {
                        val = TermLabelManager.removeIrrelevantLabels((JTerm) val,
                            node.proof().getServices());
                    } else if (val instanceof LocationVariable locVar) {
                        var originTracker = node.proof().lookup(LocationVariableTracker.class);
                        if (originTracker != null) {
                            var origin = originTracker.getCreatedBy(locVar);
                            if (origin instanceof PosTacletApp posTacletApp) {
                                var name = posTacletApp.taclet().displayName();
                                if (name.equals("ifElseUnfold") || name.equals("ifUnfold")) {
                                    val =
                                        posTacletApp.instantiations().lookupValue(new Name("#nse"));
                                }
                            }
                        }
                    }
                    res = ProofSaver.printAnything(val, node.proof().getServices());
                }
                m.appendReplacement(sb, res.replace("$", "\\$"));
            }
            m.appendTail(sb);
            // eliminate annoying whitespaces
            Pattern whiteSpacePattern = Pattern.compile("\\s+");
            Matcher whiteSpaceMatcher = whiteSpacePattern.matcher(sb);
            return whiteSpaceMatcher.replaceAll(" ");
        } else {
            return s;
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
