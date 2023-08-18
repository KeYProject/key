/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.settings;

import java.util.List;
import java.util.Set;
import javax.swing.*;

/**
 * This class encapsulates information about: 1) relative font size in the prover view 2) the
 * maximal number of lines a tooltip with instantiated SchemaVariables is allowed to have. If this
 * number is exceeded no SchemaVariables get instantiated in the displayed tooltip. 3) whether
 * intermediate proofsteps should be hidden in the proof tree view
 *
 * @author unknown
 * @author weigl
 */
public class ViewSettings extends AbstractPropertiesSettings {

    private static final String CLUTTER_RULES = "[View]clutterRules";

    private static final String CLUTTER_RULES_DEFAULT = "cut_direct_r,cut_direct_l,"
        + "case_distinction_r,case_distinction_l,local_cut,commute_and_2,commute_or_2,"
        + "boxToDiamond,pullOut,typeStatic,less_is_total,less_zero_is_total,apply_eq_monomials"
        + "eqTermCut,instAll,instEx,divIncreasingPos,divIncreasingNeg,jmodUnique1,jmodeUnique2,"
        + "jmodjmod,jmodDivisble,jdivAddMultDenom,jmodAltZero,add_non_neq_square,divide_geq,"
        + "add_greatereq,geq_add_one,leq_add_one,polySimp_addOrder,polySimp_expand,add_lesseq,"
        + "divide_equation,equal_add_one,add_eq";

    private static final String CLUTTER_RULESSETS = "[View]clutterRuleSets";

    private static final String CLUTTER_RULESETS_DEFAULT = "notHumanReadable,obsolete,"
        + "pullOutQuantifierAll,inEqSimp_commute,inEqSimp_expand,pullOutQuantifierEx,"
        + "inEqSimp_nonLin_divide,inEqSimp_special_nonLin,inEqSimp_nonLin,polySimp_normalise,"
        + "polySimp_directEquations";

    /**
     * default max number of displayed tooltip lines is 40
     */
    private static final String MAX_TOOLTIP_LINES_KEY = "[View]MaxTooltipLines";

    /**
     * Show the Load examples dialog window on startup by default
     */
    private static final String SHOW_LOAD_EXAMPLES_DIALOG = "[View]ShowLoadExamplesDialog";

    /**
     * do not print the find, varcond and heuristics part of taclets in the TacletMenu by default
     */
    private static final String SHOW_WHOLE_TACLET = "[View]ShowWholeTaclet";

    /**
     * default font size
     */
    private static final String FONT_INDEX = "[View]FontIndex";

    /**
     * do not hide intermediate proofsteps by default
     */
    private static final String HIDE_INTERMEDIATE_PROOFSTEPS = "[View]HideIntermediateProofsteps";

    private static final String HIDE_AUTOMODE_PROOFSTEPS = "[View]HideAutomodeProofsteps";

    /**
     * do not hide closed subtrees by default
     */
    private static final String HIDE_CLOSED_SUBTREES = "[View]HideClosedSubtrees";

    /**
     * Which look and feel to use.
     */
    private static final String LOOK_AND_FEEL = "[View]LookAndFeel";

    private static final String SHOW_JAVA_WARNING = "[View]ShowJavaWarning";

    /**
     * Pretty Syntax is true by default, use Unicode symbols not
     */
    private static final String PRETTY_SYNTAX = "[View]PrettySyntax";

    /**
     *
     */
    private static final String USE_UNICODE = "[View]UseUnicodeSymbols";

    /**
     *
     */
    private static final String SYNTAX_HIGHLIGHTING = "[View]SyntaxHighlighting";

    /**
     *
     */
    private static final String HIDE_PACKAGE_PREFIX = "[View]HidePackagePrefix";

    /**
     * confirm exiting by default
     */
    private static final String CONFIRM_EXIT = "[View]ConfirmExit";

    /**
     * Heatmap options property
     */
    private static final String HEATMAP_OPTIONS = "[View]HeatmapOptions";

    private static final String FONT_SIZE_FACTOR = "[View]uiFontSizeFactor";

    private static final String SEQUENT_VIEW_TOOLTIP = "[View]SequentViewTooltips";

    /** this setting enables/disables tool tips in the source view */
    private static final String SOURCE_VIEW_TOOLTIP = "[View]SourceViewTooltips";

    private static final String HIGHLIGHT_ORIGIN = "[View]HighlightOrigin";
    /**
     *
     */
    private static final String NOTIFY_LOAD_BEHAVIOUR = "[View]notifyLoadBehaviour";
    /**
     *
     */
    private static final String SHOW_UNINSTANTIATED_TACLET = "[View]showUninstantiatedTaclet";
    /**
     * Show heatmap for sequent formulas (true) or terms (false)
     */
    private static final String HEATMAP_SHOW = "[View][Heatmap]enabled";
    /**
     *
     */
    private static final String HEATMAP_SF = "[View][Heatmap]sf";
    /**
     *
     */
    private static final String HEATMAP_NEWEST = "[View][Heatmap]newest";
    /**
     *
     */
    private static final String HEATMAP_MAXAGE = "[View][Heatmap]maxAge";

    private static final String HIDE_INTERACTIVE_GOALS = "[View]hideInteractiveGoals";

    /**
     * A list of bookmark of favourite folders of the user. Can be manipulated with
     * {@link de.uka.ilkd.key.gui.KeYFileChooserBookmarkPanel}.
     */
    private static final String USER_FOLDER_BOOKMARKS = "[View]folderBookmarks";

    private static final String LOOK_AND_FEEL_DEFAULT =
        UIManager.getCrossPlatformLookAndFeelClassName();

    /**
     * Show Taclet uninstantiated in tooltip -- for learning
     */
    private final PropertyEntry<Boolean> showUninstantiatedTaclet =
        createBooleanProperty(SHOW_UNINSTANTIATED_TACLET, true);
    private final PropertyEntry<Boolean> showHeatmap = createBooleanProperty(HEATMAP_SHOW, false);
    private final PropertyEntry<Boolean> heatmapSF = createBooleanProperty(HEATMAP_SF, true);
    /**
     * Highlight newest formulas/terms (true) or all formulas/terms below specified age (false)
     */
    private final PropertyEntry<Boolean> heatmapNewest =
        createBooleanProperty(HEATMAP_NEWEST, true);
    /**
     * Maximum age/number of newest terms/formulas for heatmap highlighting
     */
    private final PropertyEntry<Integer> maxAgeForHeatmap =
        createIntegerProperty(HEATMAP_MAXAGE, 5);
    private final PropertyEntry<Double> uiFontSizeFactor =
        createDoubleProperty(FONT_SIZE_FACTOR, 1.0);
    private final PropertyEntry<Integer> maxTooltipLines =
        createIntegerProperty(MAX_TOOLTIP_LINES_KEY, 40);
    private final PropertyEntry<Boolean> hideIntermediateProofsteps =
        createBooleanProperty(HIDE_INTERMEDIATE_PROOFSTEPS, false);
    private final PropertyEntry<Boolean> hideAutomodeProofsteps =
        createBooleanProperty(HIDE_AUTOMODE_PROOFSTEPS, false);
    private final PropertyEntry<Boolean> hideClosedSubtrees =
        createBooleanProperty(HIDE_CLOSED_SUBTREES, false);
    private final PropertyEntry<Boolean> notifyLoadBehaviour =
        createBooleanProperty(NOTIFY_LOAD_BEHAVIOUR, false);
    private final PropertyEntry<Boolean> usePretty = createBooleanProperty(PRETTY_SYNTAX, true);
    private final PropertyEntry<Boolean> useUnicode = createBooleanProperty(USE_UNICODE, false);
    private final PropertyEntry<Boolean> useSyntaxHighlighting =
        createBooleanProperty(SYNTAX_HIGHLIGHTING, true);
    private final PropertyEntry<Boolean> hidePackagePrefix =
        createBooleanProperty(HIDE_PACKAGE_PREFIX, false);
    private final PropertyEntry<Boolean> confirmExit = createBooleanProperty(CONFIRM_EXIT, true);
    private final PropertyEntry<Boolean> showLoadExamplesDialog =
        createBooleanProperty(SHOW_LOAD_EXAMPLES_DIALOG, true);
    private final PropertyEntry<Boolean> showWholeTaclet =
        createBooleanProperty(SHOW_WHOLE_TACLET, false);
    private final PropertyEntry<Integer> sizeIndex = createIntegerProperty(FONT_INDEX, 2);
    private final PropertyEntry<String> lookAndFeel =
        createStringProperty(LOOK_AND_FEEL, LOOK_AND_FEEL_DEFAULT);
    private final PropertyEntry<Boolean> showSequentViewTooltips =
        createBooleanProperty(SEQUENT_VIEW_TOOLTIP, true);
    private final PropertyEntry<Boolean> showSourceViewTooltips =
        createBooleanProperty(SOURCE_VIEW_TOOLTIP, true);
    private final PropertyEntry<Boolean> highlightOrigin =
        createBooleanProperty(HIGHLIGHT_ORIGIN, true);
    private final PropertyEntry<Set<String>> clutterRules =
        createStringSetProperty(CLUTTER_RULES, CLUTTER_RULES_DEFAULT);

    private final PropertyEntry<Set<String>> clutterRuleSets =
        createStringSetProperty(CLUTTER_RULESSETS, CLUTTER_RULESETS_DEFAULT);

    private final PropertyEntry<Boolean> hideInteractiveGoals =
        createBooleanProperty(HIDE_INTERACTIVE_GOALS, false);

    /**
     * User-definable folder bookmarks.
     *
     * @see #getFolderBookmarks()
     * @see #setFolderBookmarks(List)
     */
    private final PropertyEntry<List<String>> folderBookmarks =
        createStringListProperty(USER_FOLDER_BOOKMARKS, System.getProperty("user.home"));

    /**
     * Clutter rules are rules with less priority in the taclet menu
     */
    public Set<String> getClutterRules() {
        return clutterRules.get();
    }

    public PropertyEntry<Set<String>> clutterRules() {
        return clutterRules;
    }

    public PropertyEntry<Set<String>> clutterRuleSets() {
        return this.clutterRuleSets;
    }

    /**
     * Name of rule sets containing clutter rules, which has a minor priority in the taclet menu.
     */
    public Set<String> getClutterRuleSets() {
        return clutterRuleSets.get();
    }

    /**
     * @return the current maxTooltipLines
     */
    public int getMaxTooltipLines() {
        return maxTooltipLines.get();
    }

    /**
     * Sets maxTooltipLines
     *
     * @param b The new value for maxTooltipLines
     */
    public void setMaxTooltipLines(int b) {
        maxTooltipLines.set(b);
    }

    /**
     * returns whether the "load examples" dialog should be shown on startup
     *
     * @return true iff "Load Examples" dialog should be shown
     */
    public boolean getShowLoadExamplesDialog() {
        return showLoadExamplesDialog.get();
    }

    /**
     * Sets whether the "Load Examples" dialog window should be shown on startup
     *
     * @param b indicates whether the "Load Examples" dialog window should be shown on startup or
     *        not
     */
    public void setShowLoadExamplesDialog(boolean b) {
        showLoadExamplesDialog.set(b);
    }

    /**
     * returns whether the Find and VarCond part of Taclets should be pretty-printed with
     * instantiations of schema-variables or not
     *
     * @return true iff the find part should be pretty-printed instantiated
     */
    public boolean getShowWholeTaclet() {
        return showWholeTaclet.get();
    }

    /**
     * Sets whether the Find and VarCond part of Taclets should be pretty-printed with
     * instantiations of schema-variables or not
     *
     * @param b indicates whether the Find and VarCond part of Taclets should be pretty-printed with
     *        instantiations of schema-variables or not
     */
    public void setShowWholeTaclet(boolean b) {
        showWholeTaclet.set(b);
    }

    /**
     * @return the current sizeIndex
     */
    public int sizeIndex() {
        return sizeIndex.get();
    }

    /**
     * Sets FontIndex
     *
     * @param b The new value for SizeIndex
     */
    public void setFontIndex(int b) {
        sizeIndex.set(b);
    }


    /**
     * @return class name of the look and feel to use
     */
    public String getLookAndFeel() {
        return lookAndFeel.get();
    }

    /**
     * Set which look-and-feel to use.
     *
     * @param className class name of the look and feel
     */
    public void setLookAndFeel(String className) {
        lookAndFeel.set(className);
    }

    /**
     * When loading a Java file, all other java files in the parent directory are loaded as well.
     * Should there be a notification about this when opening a file?
     *
     * @return whether to show the notification.
     */
    public boolean getNotifyLoadBehaviour() {
        return notifyLoadBehaviour.get();
    }

    /**
     * @param show Whether a notification when opening a file should be shown
     */
    public void setNotifyLoadBehaviour(boolean show) {
        notifyLoadBehaviour.set(show);
    }

    /**
     * @return true iff intermediate proof steps should be hidden
     */
    public boolean getHideIntermediateProofsteps() {
        return hideIntermediateProofsteps.get();
    }

    /**
     * @param hide Whether intermediate proof steps should be hidden
     */
    public void setHideIntermediateProofsteps(boolean hide) {
        hideIntermediateProofsteps.set(hide);
    }

    /**
     * @return true iff non-interactive proof steps should be hidden
     */
    public boolean getHideAutomodeProofsteps() {
        return hideAutomodeProofsteps.get();
    }

    /**
     * @param hide Whether non-interactive proof steps should be hidden
     */
    public void setHideAutomodeProofsteps(boolean hide) {
        hideAutomodeProofsteps.set(hide);
    }

    /**
     * @return true iff closed subtrees should be hidden
     */
    public boolean getHideClosedSubtrees() {
        return hideClosedSubtrees.get();
    }

    /**
     * @param hide Whether closed subtrees should be hidden
     */
    public void setHideClosedSubtrees(boolean hide) {
        hideClosedSubtrees.set(hide);
    }

    public boolean isUsePretty() {
        return usePretty.get();
    }

    public void setUsePretty(boolean usePretty) {
        if (!usePretty) {
            setUseUnicode(false);
        }
        this.usePretty.set(usePretty);
    }

    /**
     * Use Unicode Symbols is only allowed if pretty syntax is used
     *
     * @return setting of use unicode symbols (if use pretty syntax is on, return the value which is
     *         set, if use retty is false, return false)
     */
    public boolean isUseUnicode() {
        if (isUsePretty()) {
            return useUnicode.get();
        } else {
            setUseUnicode(false);
            return false;
        }
    }

    public void setUseUnicode(boolean useUnicode) {
        // unicode requires pretty
        useUnicode = useUnicode && usePretty.get();
        this.useUnicode.set(useUnicode);
    }

    public boolean isUseSyntaxHighlighting() {
        return useSyntaxHighlighting.get();
    }

    public void setUseSyntaxHighlighting(boolean enable) {
        this.useSyntaxHighlighting.set(enable);
    }

    public boolean isHidePackagePrefix() {
        return hidePackagePrefix.get();
    }

    public void setHidePackagePrefix(boolean hide) {
        hidePackagePrefix.set(hide);
    }

    /**
     * Whether to display the confirmation dialog upon exiting the main window.
     */
    public boolean confirmExit() {
        return confirmExit.get();
    }

    /**
     * Set whether to display the confirmation dialog upon exiting the main window.
     */
    public void setConfirmExit(boolean confirmExit) {
        this.confirmExit.set(confirmExit);
    }

    public boolean getShowUninstantiatedTaclet() {
        return showUninstantiatedTaclet.get();
    }

    public void setShowUninstantiatedTaclet(boolean b) {
        showUninstantiatedTaclet.set(b);
    }

    /**
     * @return whether heatmaps should be displayed
     */
    public boolean isShowHeatmap() {
        return showHeatmap.get();
    }

    /**
     * Updates heatmap settings (all of the at the same time, so that fireSettingsChanged is called
     * only once.
     *
     * @param showHeatmap true if heatmap on
     * @param heatmapSF true for sequent formulas, false for terms
     * @param heatmapNewest true if newest, false for "up to age"
     * @param maxAgeForHeatmap the maximum age for term or sequent formulas, concerning heatmap
     *        highlighting
     */
    public void setHeatmapOptions(boolean showHeatmap, boolean heatmapSF, boolean heatmapNewest,
            int maxAgeForHeatmap) {
        this.showHeatmap.set(showHeatmap);
        this.heatmapSF.set(heatmapSF);
        this.heatmapNewest.set(heatmapNewest);
        this.maxAgeForHeatmap.set(maxAgeForHeatmap);
    }

    /**
     * @return whether sequent formulas or terms should be highlighted
     */
    public boolean isHeatmapSF() {
        return heatmapSF.get();
    }

    /**
     * @return whether to highlight "newest" or "up to age"
     */
    public boolean isHeatmapNewest() {
        return heatmapNewest.get();
    }

    /**
     * @return the maximum age for term or sequent formulas, concerning heatmap highlighting
     */
    public int getMaxAgeForHeatmap() {
        return maxAgeForHeatmap.get();
    }

    public boolean isHighlightOrigin() {
        return highlightOrigin.get();
    }

    public void setHighlightOrigin(boolean highlightOrigin) {
        this.highlightOrigin.set(highlightOrigin);
    }

    public boolean isShowSequentViewTooltips() {
        return showSequentViewTooltips.get();
    }

    public void setShowSequentViewTooltips(boolean showSequentViewTooltips) {
        this.showSequentViewTooltips.set(showSequentViewTooltips);
    }

    public boolean isShowSourceViewTooltips() {
        return showSourceViewTooltips.get();
    }

    public void setShowSourceViewTooltips(boolean showSourceViewTooltips) {
        this.showSourceViewTooltips.set(showSourceViewTooltips);
    }

    public double getUIFontSizeFactor() {
        return uiFontSizeFactor.get();
    }

    public void setUIFontSizeFactor(double factor) {
        this.uiFontSizeFactor.set(factor);
    }


    public boolean getHideInteractiveGoals() {
        return hideInteractiveGoals.get();
    }

    public void setHideInteractiveGoals(boolean active) {
        hideInteractiveGoals.set(active);
    }

    /**
     * @see #folderBookmarks
     */
    public List<String> getFolderBookmarks() {
        return folderBookmarks.get();
    }

    /**
     * @see #folderBookmarks
     */
    public void setFolderBookmarks(List<String> bm) {
        folderBookmarks.set(bm);
    }
}
