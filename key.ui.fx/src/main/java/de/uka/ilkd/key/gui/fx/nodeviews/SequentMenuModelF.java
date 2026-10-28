/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.nodeviews;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.java.visitor.JavaASTWalker;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.op.FormulaSV;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.join.ProspectivePartner;
import de.uka.ilkd.key.rule.BlockContractExternalRule;
import de.uka.ilkd.key.rule.BlockContractInternalRule;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.LoopContractExternalRule;
import de.uka.ilkd.key.rule.LoopContractInternalRule;
import de.uka.ilkd.key.rule.LoopScopeInvariantRule;
import de.uka.ilkd.key.rule.NoFindTaclet;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.TacletSchemaVariableCollector;
import de.uka.ilkd.key.rule.UseOperationContractRule;
import de.uka.ilkd.key.rule.WhileInvariantRule;
import de.uka.ilkd.key.rule.merge.MergeRule;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.settings.FeatureSettings;
import de.uka.ilkd.key.settings.ProofIndependentSMTSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.smt.SolverTypeCollection;

import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.proof.rulefilter.TacletFilter;
import org.key_project.prover.rules.RuleSet;
import org.key_project.prover.rules.tacletbuilder.TacletGoalTemplate;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/**
 * Pure-Java model of the menu shown when the user right-clicks a term, operator or sequent in the
 * sequent view. This is the FX counterpart of the Swing {@code
 * de.uka.ilkd.key.gui.nodeviews.CurrentGoalViewMenu} (key.ui, {@code CurrentGoalViewMenu.java},
 * the whole menu logic) plus the context-menu contributions of the Swing base
 * {@code SequentViewMenu}.
 * <p>
 * The model is deliberately free of any Swing or JavaFX types: it reduces the applicable rules,
 * built-in rules and menu structure at a {@link PosInSequent} to a tree of {@link Entry
 * descriptors}. The concrete UI (a JavaFX {@code ContextMenu}) is built from those descriptors by
 * the companion shell {@code SequentTermContextMenuF}, which also supplies the FX- or
 * side-effectful pieces (macro list, extension actions, clipboard, SMT launch) via the {@link
 * Seam} supplier so that this class stays headlessly unit-testable.
 * <p>
 * Rule applicability is computed through the same {@link ProofControl} query surface the Swing
 * listener uses ({@code getBuiltInRule}, {@code getFindTaclet}, {@code getRewriteTaclet},
 * {@code getNoFindTaclet}), so the two produce the same rule lists for a given goal and position.
 */
public final class SequentMenuModelF {

    /** The Swing name of the (unsound, hidden by default) axiom-introduction taclet. */
    public static final String INTRODUCE_AXIOM_TACLET_NAME = "introduceAxiom";

    public static final String MORE_RULES = "More rules";
    public static final String APPLY_CONTRACT = "Apply Contract";
    public static final String CHOOSE_AND_APPLY_CONTRACT = "Choose and Apply Contract...";
    public static final String ENTER_LOOP_SPECIFICATION = "Enter Loop Specification...";
    public static final String APPLY_RULE = "Apply Rule";
    public static final String NO_RULES_APPLICABLE = "No rules applicable.";
    public static final String INSERT_CLASS_INVARIANT = "Insert Class Invariant";
    public static final String INSERT_HIDDEN = "Insert Hidden";

    /** The Swing FeatureSettings id that gates the delayed-cut join entry. */
    public static final String FEATURE_DELAY_CUT = "DELAY_CUT";

    /** Pagination threshold for the flat taclet list (Swing {@code TOO_MANY_TACLETS_THRESHOLD}). */
    public static final int TOO_MANY_TACLETS_THRESHOLD = 15;

    /** Sort order for the taclet list (Swing {@code CurrentGoalViewMenu.TacletAppComparator}). */
    public static final Comparator<TacletApp> TACLET_SORT = new TacletAppComparator();

    /** The position at which the menu was requested. {@code null} for a whole-sequent menu. */
    private final @Nullable PosInSequent pos;

    private final KeYMediatorF mediator;
    private final ProofControl proofControl;
    private final @Nullable Seam seam;
    private final @Nullable TacletFilter interactiveFilter;

    /**
     * Pluggable, side-effectful or UI-dependent menu contributions that the pure model cannot (and
     * must not) compute itself. The FX shell supplies real implementations; unit tests supply
     * stubs or {@code null} to skip.
     */
    public interface Seam {
        /** Name-creation-info OSS/abbreviation UI hooks used by the abbreviation section. */
        @NonNull
        AbbrevHooks abbrevHooks();

        /**
         * The visual candidate action for a single applicable {@link TacletApp} (Swing
         * {@code TacletAppAction}): rendered label and full tooltip text.
         */
        @NonNull
        TacletHooks tacletHooks();
    }

    /** Abbreviation-map action labels that the model emits as descriptors when applicable. */
    public interface AbbrevHooks {
        String createLabel();

        String changeLabel();

        String enableLabel();

        String disableLabel();
    }

    /** Presentation hooks for an applicable taclet (label + tooltip). */
    public interface TacletHooks {
        /** The menu label for the taclet (Swing {@code TacletAppAction.setName}). */
        @NonNull
        String label(TacletApp app);

        /** The (raw, possibly HTML) tooltip for the taclet. */
        @NonNull
        String tooltip(TacletApp app);
    }

    /**
     * Result tree of the model. Each {@link Entry} is one of: a taclet application, a built-in
     * rule application (possibly with two sub-entries), a sub-menu, a fixed named action, an
     * abbreviation action, or a separator.
     */
    public sealed interface Entry permits TacletEntry, BuiltInEntry, SubMenuEntry, NamedAction,
            SeparatorEntry, AbbrevActionEntry {

        /** A symbolic discriminator so the FX shell can switch without instanceof chains. */
        Kind kind();

        enum Kind {
            TACLET, BUILT_IN, SUB_MENU, NAMED_ACTION, ABBREV_ACTION, SEPARATOR
        }
    }

    /** A single applicable taclet application. */
    public record TacletEntry(@NonNull Kind kind, @NonNull TacletApp app, @NonNull String label,
            @NonNull String tooltip) implements Entry {
        public TacletEntry(TacletApp app, String label, String tooltip) {
            this(Kind.TACLET, app, label, tooltip);
        }
    }

    /**
     * A built-in rule entry. Built-in rules that support both a "forced/complete" and an
     * "interactive" mode contribute two labeled sub-actions (e.g. the contract and loop rules); all
     * others contribute a single action. {@code forced} only selects the mode, never what rule to
     * run.
     */
    public record BuiltInEntry(@NonNull Kind kind, @NonNull BuiltInRule rule,
            @NonNull List<@NonNull NamedAction> actions, @NonNull String subMenuLabel)
            implements Entry {
        public BuiltInEntry(BuiltInRule rule, List<NamedAction> actions, String subMenuLabel) {
            this(Kind.BUILT_IN, rule, List.copyOf(actions), subMenuLabel);
        }
    }

    /**
     * A sub-menu node ({@code More rules}, {@code Insert Hidden}, {@code Insert Class Invariant}).
     */
    public record SubMenuEntry(@NonNull Kind kind, @NonNull String label,
            @NonNull List<@NonNull Entry> children) implements Entry {
        public SubMenuEntry(String label, List<Entry> children) {
            this(Kind.SUB_MENU, label, List.copyOf(children));
        }
    }

    /**
     * A fixed-named action emitted by the model. The FX shell maps each {@code id} to a concrete
     * handler (merge rule, join, focused auto mode, SMT union, copy to clipboard, view name
     * creation info, a macro, an extension action).
     */
    public record NamedAction(@NonNull Kind kind, @NonNull String id, @NonNull String label,
            @Nullable String tooltip, @Nullable Object payload) implements Entry {
        public NamedAction(String id, String label, String tooltip, Object payload) {
            this(Kind.NAMED_ACTION, id, label, tooltip, payload);
        }
    }

    /** A named abbreviation action (create/change/enable/disable). */
    public record AbbrevActionEntry(@NonNull Kind kind, @NonNull AbbrevAction action,
            @NonNull String label) implements Entry {
        public AbbrevActionEntry(AbbrevAction action, String label) {
            this(Kind.ABBREV_ACTION, action, label);
        }
    }

    public enum AbbrevAction {
        CREATE, CHANGE, ENABLE, DISABLE
    }

    /** A visual menu separator. */
    public record SeparatorEntry(@NonNull Kind kind) implements Entry {
        public SeparatorEntry() {
            this(Kind.SEPARATOR);
        }
    }

    private SequentMenuModelF(@Nullable PosInSequent pos, KeYMediatorF mediator,
            ProofControl proofControl, @Nullable Seam seam,
            @Nullable TacletFilter interactiveFilter) {
        this.pos = pos;
        this.mediator = mediator;
        this.proofControl = proofControl;
        this.seam = seam;
        this.interactiveFilter = interactiveFilter;
    }

    /**
     * Builds the menu that Swing {@code CurrentGoalViewMenu} would show for the given position.
     * Each constructor parameter mirrors the Swing inputs:
     *
     * @param pos the selected {@link PosInSequent} (possibly {@code null})
     * @param mediator the FX mediator (selection, notation info, services)
     * @param proofControl the consulted {@link ProofControl} (rule applicability)
     * @param seam optional UI hooks; {@code null} skips abbreviation/taclet styling
     * @param interactiveFilter the Interactive-Proof filter (Swing
     *        {@code KeYMediator#getFilterForInteractiveProving}); {@code null}
     *        keeps every taclet that survives the clutter rules
     * @return the ordered root entries of the context menu
     */
    public static @NonNull List<@NonNull Entry> build(@Nullable PosInSequent pos,
            @NonNull KeYMediatorF mediator, @NonNull ProofControl proofControl,
            @Nullable Seam seam, @Nullable TacletFilter interactiveFilter) {
        SequentMenuModelF m = new SequentMenuModelF(pos, mediator, proofControl, seam,
            interactiveFilter);
        return m.compute();
    }

    private List<Entry> compute() {
        // The Swing listener computes the four lists via the proof control, keyed on the clicked
        // position (CurrentGoalViewListener.java:72-83). We mirror that exactly.
        Goal goal = mediator.getSelectedGoal();
        PosInOccurrence pio = pos != null ? pos.getPosInOccurrence() : null;

        // Match the Swing guard: only compute when we have a goal AND (pos.sequent xor
        // pio != null). The Swing path only reaches a menu with a valid combination; we guard to
        // avoid NPEs on a position whose occurrence is not resolvable in the current goal.
        if (goal == null) {
            return List.of();
        }

        List<Entry> result = new ArrayList<>();

        ImmutableList<BuiltInRule> builtInList = proofControl.getBuiltInRule(goal, pio);
        ImmutableList<TacletApp> findList = proofControl.getFindTaclet(goal, pio);
        ImmutableList<TacletApp> rewriteList = proofControl.getRewriteTaclet(goal, pio);
        ImmutableList<TacletApp> noFindList = proofControl.getNoFindTaclet(goal);

        // delete RewriteTaclets from findList because they will be in the rewrite list, and
        // concatenate both lists (Swing CurrentGoalViewMenu constructor).
        ImmutableList<TacletApp> combined =
            removeRewrites(findList).prepend(rewriteList);
        ImmutableList<TacletApp> noFind = removeIntroduceAxiomTaclet(noFindList);

        // "immediate" section: applicable taclets at the clicked position.
        boolean sequentPos = pos != null && pos.isSequent();
        ImmutableList<TacletApp> toAdd = sort(combined, TACLET_SORT);
        boolean rulesAvailable = !combined.isEmpty();
        if (sequentPos) {
            rulesAvailable |= !noFind.isEmpty();
            toAdd = toAdd.prepend(noFind);
        }

        if (rulesAvailable) {
            addTacletSection(result, toAdd);
        } else {
            result.add(new NamedAction("no_rules", NO_RULES_APPLICABLE, null, null));
        }

        addBuiltInSection(result, builtInList);

        // delayed-cut join (Swing CurrentGoalViewMenu.createDelayedCutJoinMenu)
        if (FeatureSettings.isFeatureActivated(FEATURE_DELAY_CUT)) {
            if (sequentPos && pio != null) {
                Collection<ProspectivePartner> partner =
                    de.uka.ilkd.key.proof.join.JoinIsApplicable.INSTANCE.isApplicable(goal, pio);
                if (!partner.isEmpty()) {
                    result.add(new NamedAction("join", joinLabel(partner.size()),
                        "Delayed-cut join of the highlighted term.", partner));
                }
            }
        }

        // merge rule (Swing createMergeRuleMenu)
        if (sequentPos && pio != null
                && MergeRule.isOfAdmissibleForm(goal, pio, true)) {
            result.add(new NamedAction("merge_rule", mergeLabel(), mergeTooltip(), pio));
        }

        // SMT (Swing createSMTMenu) — only on a sequent position
        if (sequentPos) {
            addSMTSection(result);
        }

        addFocussedAutoMode(result);

        result.add(new NamedAction("macro_menu", "Strategy Macros", null, null));

        result.add(new SeparatorEntry());

        result.add(new NamedAction("extension", "Extensions", null, null));

        result.add(new SeparatorEntry());

        result.add(new NamedAction("copy_clipboard", "Copy to clipboard", null, null));

        // Term-relative sections (abbreviation, name creation info)
        if (pos != null) {
            PosInOccurrence occ = pos.getPosInOccurrence();
            if (occ != null && occ.posInTerm() != null) {
                JTerm sub = (JTerm) occ.subTerm();
                addAbbrevSection(result, sub);

                if (sub.op() instanceof ProgramVariable var) {
                    if (var.getProgramElementName().getCreationInfo() != null) {
                        result.add(new NamedAction("name_creation_info", "View name creation info",
                            null, var));
                    }
                }
            }
        }

        return List.copyOf(result);
    }

    private String joinLabel(int partnerCount) {
        return "Join (" + partnerCount + (partnerCount == 1 ? " partner)" : " partners)");
    }

    private @NonNull String mergeLabel() {
        return "Refocus merge rule";
    }

    private @NonNull String mergeTooltip() {
        return "Links a partner node to this merged node (Swing MergeRuleMenuItem)";
    }

    private void addTacletSection(List<Entry> out, ImmutableList<TacletApp> taclets) {
        List<TacletApp> hidden = new ArrayList<>();
        List<TacletApp> systemInv = new ArrayList<>();
        List<TacletApp> normal = new ArrayList<>();
        List<TacletApp> rare = new ArrayList<>();

        Set<String> clutterRuleSets = viewSettings().getClutterRuleSets();
        Set<String> clutterRules = viewSettings().getClutterRules();

        for (TacletApp app : taclets) {
            Taclet taclet = app.taclet();
            if (isHiddenTaclet(taclet)) {
                hidden.add(app);
                continue;
            }
            if (isSystemInvariantTaclet(taclet)) {
                systemInv.add(app);
                continue;
            }
            if (interactiveFilter != null && !interactiveFilter.filter(taclet)) {
                continue;
            }
            if (isRareRule(taclet, clutterRuleSets, clutterRules)) {
                rare.add(app);
            } else {
                normal.add(app);
            }
        }
        normal.addAll(rare);

        int currentSize = 0;
        List<Entry> target = out;
        for (TacletApp app : normal) {
            target.add(createTacletEntry(app));
            ++currentSize;
            if (currentSize >= TOO_MANY_TACLETS_THRESHOLD) {
                List<Entry> sub = new ArrayList<>();
                target.add(new SubMenuEntry(MORE_RULES, sub));
                target = sub;
                currentSize = 0;
            }
        }

        if (!hidden.isEmpty()) {
            out.add(createInsertHiddenMenu(hidden));
        }
        if (!systemInv.isEmpty()) {
            out.add(createSystemInvariantMenu(systemInv));
        }
    }

    private Entry createTacletEntry(TacletApp app) {
        String label = app.taclet().displayName();
        String tooltip = "";
        if (seam != null) {
            label = seam.tacletHooks().label(app);
            tooltip = seam.tacletHooks().tooltip(app);
        }
        return new TacletEntry(app, label, tooltip);
    }

    private void addBuiltInSection(List<Entry> out, ImmutableList<BuiltInRule> builtInList) {
        if (builtInList.isEmpty()) {
            return;
        }
        out.add(new SeparatorEntry());
        for (BuiltInRule rule : builtInList) {
            addBuiltInRule(out, rule);
        }
    }

    private void addBuiltInRule(List<Entry> out, BuiltInRule rule) {
        switch (rule) {
            case WhileInvariantRule r -> out.add(dualEntry(rule, APPLY_RULE,
                "Applies a known and complete loop specification immediately.",
                ENTER_LOOP_SPECIFICATION,
                "Allows to modify an existing or to enter a new loop specification."));
            case BlockContractInternalRule r -> out.add(dualEntry(rule, APPLY_RULE,
                "Applies a known and complete block specification immediately.",
                CHOOSE_AND_APPLY_CONTRACT, "Asks to select the contract to be applied."));
            case BlockContractExternalRule r -> out.add(dualEntry(rule, APPLY_RULE,
                "All available contracts of the block are combined and applied.",
                CHOOSE_AND_APPLY_CONTRACT, "Asks to select the contract to be applied."));
            case LoopContractInternalRule r -> out.add(dualEntry(rule, APPLY_RULE,
                "Applies a known and complete loop block specification immediately.",
                CHOOSE_AND_APPLY_CONTRACT, "Asks to select the contract to be applied."));
            case LoopContractExternalRule r -> out.add(dualEntry(rule, APPLY_RULE,
                "All available contracts of the loop block are combined and applied.",
                CHOOSE_AND_APPLY_CONTRACT, "Asks to select the contract to be applied."));
            case UseOperationContractRule r -> out.add(dualEntry(rule, APPLY_CONTRACT,
                "All available contracts of the method are combined and applied.",
                CHOOSE_AND_APPLY_CONTRACT, "Asks to select the contract to be applied."));
            case MergeRule r -> {
                // handled by the merge-rule entry elsewhere; nothing extra here
            }
            case LoopScopeInvariantRule r -> {
            }
            case null -> {
            }
            default -> out.add(new BuiltInEntry(rule,
                List.of(new NamedAction("apply_builtin_forced", rule.toString(), "", rule)),
                ""));
        }
    }

    private Entry dualEntry(BuiltInRule rule, String forcedText, String forcedTip,
            String interactiveText, String interactiveTip) {
        List<NamedAction> actions = List.of(
            new NamedAction("apply_builtin_forced", forcedText, forcedTip, rule),
            new NamedAction("apply_builtin_interactive", interactiveText, interactiveTip, rule));
        return new BuiltInEntry(rule, actions, null);
    }

    private void addFocussedAutoMode(List<Entry> out) {
        out.add(new SeparatorEntry());
        out.add(new NamedAction("focus_auto_mode", "Apply rules automatically here",
            "Initiates and restricts automatic rule applications on the highlighted formula, "
                + "term or sequent.  'Shift + left mouse click' on the highlighted entity does the same.",
            pos));
    }

    private void addSMTSection(List<Entry> out) {
        ProofIndependentSMTSettings smt =
            ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings();
        Collection<SolverTypeCollection> solverUnions = smt.getSolverUnions();
        if (!solverUnions.isEmpty()) {
            out.add(new SeparatorEntry());
        }
        for (SolverTypeCollection union : solverUnions) {
            if (union.isUsable()) {
                out.add(
                    new NamedAction("smt", union.toString(), "Run the " + union + " SMT solvers.",
                        union));
            }
        }
    }

    private boolean addAbbrevSection(List<Entry> out, JTerm t) {
        AbbrevMap map = mediator.getNotationInfo().getAbbrevMap();
        AbbrevHooks hooks = seam != null ? seam.abbrevHooks() : null;
        String create = hooks != null ? hooks.createLabel() : "Create abbreviation...";
        String change = hooks != null ? hooks.changeLabel() : "Change abbreviation...";
        String enable = hooks != null ? hooks.enableLabel() : "Enable abbreviation";
        String disable = hooks != null ? hooks.disableLabel() : "Disable abbreviation";
        if (map.containsTerm(t)) {
            out.add(new AbbrevActionEntry(AbbrevAction.CHANGE, change));
            out.add(
                new AbbrevActionEntry(map.isEnabled(t) ? AbbrevAction.DISABLE : AbbrevAction.ENABLE,
                    map.isEnabled(t) ? disable : enable));
        } else {
            out.add(new AbbrevActionEntry(AbbrevAction.CREATE, create));
        }
        return true;
    }

    private Entry createInsertHiddenMenu(List<TacletApp> hidden) {
        List<Entry> children = new ArrayList<>();
        for (TacletApp app : hidden) {
            children.add(createTacletEntry(app));
        }
        return new SubMenuEntry(INSERT_HIDDEN, children);
    }

    private Entry createSystemInvariantMenu(List<TacletApp> systemInv) {
        systemInv.sort(Comparator.comparing(it -> it.taclet().displayName()));
        List<Entry> children = new ArrayList<>();
        for (TacletApp app : systemInv) {
            children.add(createTacletEntry(app));
        }
        return new SubMenuEntry(INSERT_CLASS_INVARIANT, children);
    }

    // ---------------------------------------------------------------------------------------------
    // Static rule-classification helpers (verbatim logic from CurrentGoalViewMenu /
    // SequentViewMenu)
    // ---------------------------------------------------------------------------------------------

    /**
     * Removes the unsound "introduceAxiom" taclet from the list of displayed taclets
     * (Swing CurrentGoalViewMenu.removeIntroduceAxiomTaclet).
     */
    public static ImmutableList<TacletApp> removeIntroduceAxiomTaclet(
            ImmutableList<TacletApp> list) {
        return list.stream()
                .filter(app -> !app.rule().name().toString().equals(INTRODUCE_AXIOM_TACLET_NAME))
                .collect(ImmutableList.collector());
    }

    /** Removes {@link RewriteTaclet}s from a list (Swing CurrentGoalViewMenu.removeRewrites). */
    public static ImmutableList<TacletApp> removeRewrites(ImmutableList<TacletApp> list) {
        ImmutableList<TacletApp> result = ImmutableList.nil();
        for (TacletApp app : list) {
            Taclet taclet = app.taclet();
            result = (taclet instanceof RewriteTaclet ? result : result.prepend(app));
        }
        return result;
    }

    /**
     * Sorts {@code finds} with {@code comp} — intentionally <em>reversing</em> the comparator's
     * natural order, because the Swing method prepends the sorted list back together (Swing
     * CurrentGoalViewMenu.sort, "the order will be reversed when the list is sorted"). Kept
     * byte-identical so headless assertions can mirror the Swing output exactly.
     */
    public static ImmutableList<TacletApp> sort(ImmutableList<TacletApp> finds,
            Comparator<TacletApp> comp) {
        ImmutableList<TacletApp> result = ImmutableList.nil();
        List<TacletApp> list = new ArrayList<>(finds.size());
        for (TacletApp app : finds) {
            list.add(app);
        }
        list.sort(comp);
        for (TacletApp app : list) {
            result = result.prepend(app);
        }
        return result;
    }

    /**
     * "Insert hidden" taclets are {@code NoFindTaclet}s whose display name starts with
     * {@code insert_hidden} and which have exactly one goal template (Swing
     * CurrentGoalViewMenu.isHiddenTaclet).
     */
    public static boolean isHiddenTaclet(Taclet taclet) {
        if (!(taclet instanceof NoFindTaclet)
                || !taclet.displayName().startsWith("insert_hidden")) {
            return false;
        }
        return taclet.goalTemplates().size() == 1;
    }

    /**
     * "Insert class invariant" taclets are {@code NoFindTaclet}s whose display name starts with
     * {@code Insert implicit invariants of} and which have exactly one goal template (Swing
     * CurrentGoalViewMenu.isSystemInvariantTaclet).
     */
    public static boolean isSystemInvariantTaclet(Taclet taclet) {
        if (!(taclet instanceof NoFindTaclet)
                || !taclet.displayName().startsWith("Insert implicit invariants of")) {
            return false;
        }
        return taclet.goalTemplates().size() == 1;
    }

    private static boolean isRareRule(Taclet taclet, Set<String> clutterRules,
            Set<String> clutterRuleSets) {
        if (clutterRules.contains(taclet.name().toString())) {
            return true;
        }
        return taclet.getRuleSets().stream()
                .anyMatch(it -> clutterRuleSets.contains(it.name().toString()));
    }

    private de.uka.ilkd.key.settings.ViewSettings viewSettings() {
        return ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings();
    }

    // ---------------------------------------------------------------------------------------------
    // TacletAppComparator (verbatim port of Swing CurrentGoalViewMenu.TacletAppComparator)
    // ---------------------------------------------------------------------------------------------

    /**
     * Orders applicable taclets so the "best" heuristic candidate appears near the top of the menu
     * (Swing {@code CurrentGoalViewMenu.TacletAppComparator}). The comparator itself is used <em>by
     * {@link #sort}</em>, whose reversal makes a <em>smaller</em> score sort <em>later</em>; the
     * resulting order is what the Swing menu shows. This nested class is {@code public} to be
     * unit-tested independently, matching the Swing class's visibility.
     */
    public static final class TacletAppComparator implements Comparator<TacletApp> {

        private int countFormulaSV(TacletSchemaVariableCollector c) {
            int formulaSV = 0;
            Iterator<SchemaVariable> it = c.varIterator();
            while (it.hasNext()) {
                SchemaVariable sv = it.next();
                if (sv instanceof FormulaSV) {
                    formulaSV++;
                }
            }
            return formulaSV;
        }

        /** Rough goal complexity estimate (Swing measureGoalComplexity). */
        private int measureGoalComplexity(ImmutableList<TacletGoalTemplate> l) {
            int result = 0;
            for (TacletGoalTemplate gt : l) {
                if (gt instanceof RewriteTacletGoalTemplate) {
                    if (((RewriteTacletGoalTemplate) gt).replaceWith() != null) {
                        result += ((RewriteTacletGoalTemplate) gt).replaceWith().depth();
                    }
                }
                if (!gt.sequent().isEmpty()) {
                    result += 10;
                }
            }
            return result;
        }

        /** Rough program-size estimate (Swing programComplexity). */
        public int programComplexity(JavaBlock b) {
            if (b.isEmpty()) {
                return 0;
            }
            return new JavaASTWalker(b.program()) {
                private int counter = 0;

                @Override
                protected void doAction(de.uka.ilkd.key.java.ast.ProgramElement pe) {
                    counter++;
                }

                public int getCounter() {
                    counter = 0;
                    start();
                    return counter;
                }
            }.getCounter();
        }

        @Override
        public int compare(TacletApp o1, TacletApp o2) {
            LinkedHashMap<String, Integer> map1 = score(o1);
            LinkedHashMap<String, Integer> map2 = score(o2);
            Iterator<Map.Entry<String, Integer>> it1 = map1.entrySet().iterator();
            Iterator<Map.Entry<String, Integer>> it2 = map2.entrySet().iterator();
            while (it1.hasNext() && it2.hasNext()) {
                String s1 = it1.next().getKey();
                String s2 = it2.next().getKey();
                if (!s1.equals(s2)) {
                    throw new IllegalStateException(
                        "A decision should have been made on a higher level ( " + s1 + "<->" + s2
                            + ")");
                }
                int v1 = map1.get(s1);
                int v2 = map2.get(s2);
                if (v1 < v2) {
                    return 1;
                }
                if (v1 > v2) {
                    return -1;
                }
            }
            return 0;
        }

        /** A named, lexicographically comparable score for one taclet (Swing score). */
        public LinkedHashMap<String, Integer> score(TacletApp o1) {
            LinkedHashMap<String, Integer> map = new LinkedHashMap<>();
            final Taclet taclet1 = o1.taclet();

            map.put("closing", taclet1.goalTemplates().isEmpty() ? -1 : 1);

            boolean calc = false;
            for (RuleSet rs : taclet1.getRuleSets()) {
                String s = rs.name().toString();
                if (s.equals("simplify_literals") || s.equals("concrete") || s.equals("update_elim")
                        || s.equals("replace_known_left") || s.equals("replace_known_right")) {
                    calc = true;
                }
            }
            map.put("calc", calc ? -1 : 1);

            int formulaSV1 = 0;
            int cmpVar1 = 0;

            if (taclet1 instanceof FindTaclet) {
                map.put("has_find", -1);
                final JTerm find1 = ((FindTaclet) taclet1).find();
                int findComplexity1 = find1.depth();
                findComplexity1 += programComplexity(find1.javaBlock());
                map.put("find_complexity", -findComplexity1);

                TacletSchemaVariableCollector coll1 = new TacletSchemaVariableCollector();
                find1.execPostOrder(coll1);
                formulaSV1 = countFormulaSV(coll1);
                cmpVar1 -= coll1.size();
                map.put("num_sv", -cmpVar1);
            } else {
                map.put("has_find", 1);
            }

            cmpVar1 = cmpVar1 - formulaSV1;
            map.put("sans_formula_sv", -cmpVar1);

            map.put("if_seq", taclet1.assumesSequent().isEmpty() ? 1 : -1);
            map.put("num_goals", taclet1.goalTemplates().size());
            map.put("goal_compl", measureGoalComplexity(taclet1.goalTemplates()));

            return map;
        }
    }
}
