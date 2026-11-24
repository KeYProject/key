/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.colors;

import javafx.scene.paint.Color;

/**
 * The full Swing-parity color palette of KeY, mirroring every
 * {@code ColorSettings.define(...)} call site of the Swing module {@code key.ui}.
 * <p>
 * The Swing UI registers {@code de.uka.ilkd.key.gui.colors.ColorSettings.ColorProperty}
 * instances at class-load time of the classes that use them (the lexers, the source view, the
 * proof tree, {@code SolverListener}, ...). The FX counterpart {@link ColorSettingsF} is a
 * plain registry without such consumers, so this class holds one static
 * {@link ColorSettingsF.ColorPropertyF}
 * per Swing call site with the identical key and defaults. The properties are registered in
 * {@link ColorSettingsF} as soon as this class is loaded; {@link #ensureRegistered()} is a
 * class-load bootstrap used by the {@code getInstance()} wiring of {@link ColorSettingsF} and
 * by the {@code key.fx.verify.colors} self test.
 * <p>
 * The keys and the per-theme defaults are the ones of the Swing {@code define} calls, so
 * {@code colors.json} files written by the Swing UI round-trip unchanged (unmapped keys are
 * preserved by {@link ColorSettingsF#save()}). Keys whose visuals have no FX counterpart yet
 * (e.g. {@code [currentGoal]*}, {@code [innerNodeView]*}, the heatmap base color) are
 * configurable in the colors panel but have no rendering effect here — see the
 * {@code CSS_VARIABLES} documentation.
 */
public final class ColorPaletteF {

    private ColorPaletteF() {
    }

    /**
     * Forces the static registration of the whole palette. Empty on purpose: loading this class
     * runs the static initializers.
     */
    public static void ensureRegistered() {
    }

    // ------------------------------------------------------------------
    // infotree (Swing: utilities/LexerHighlighter)
    // ------------------------------------------------------------------

    /** Syntax color of keywords in the info tree (Swing {@code infotree.syntax.keyword}). */
    public static final ColorSettingsF.ColorPropertyF INFOTREE_KEYWORD =
        define("infotree.syntax.keyword", "Keywords in the rule/symbol browser",
            Color.rgb(0, 0, 255), Color.rgb(255, 165, 0));

    /** Syntax color of identifiers in the info tree (Swing {@code infotree.syntax.identifier}). */
    public static final ColorSettingsF.ColorPropertyF INFOTREE_IDENTIFIER =
        define("infotree.syntax.identifier", "Identifiers in the rule/symbol browser",
            Color.rgb(0, 0, 0), Color.rgb(255, 255, 255));

    /** Syntax color of comments in the info tree (Swing {@code infotree.syntax.comment}). */
    public static final ColorSettingsF.ColorPropertyF INFOTREE_COMMENT =
        define("infotree.syntax.comment", "Comments in the rule/symbol browser",
            Color.rgb(0, 128, 0));

    /** Syntax color of operators in the info tree (Swing {@code infotree.syntax.operators}). */
    public static final ColorSettingsF.ColorPropertyF INFOTREE_OPERATORS =
        define("infotree.syntax.operators", "Operators in the rule/symbol browser",
            Color.rgb(0, 0, 0), Color.rgb(255, 165, 0));

    /** Syntax color of errors in the info tree (Swing {@code infotree.syntax.error}). */
    public static final ColorSettingsF.ColorPropertyF INFOTREE_ERROR =
        define("infotree.syntax.error", "Syntax errors in the rule/symbol browser",
            Color.rgb(255, 0, 0), Color.rgb(255, 255, 255));

    /** Syntax color of literals in the info tree (Swing {@code infotree.syntax.literals}). */
    public static final ColorSettingsF.ColorPropertyF INFOTREE_LITERALS =
        define("infotree.syntax.literals", "Literals in the rule/symbol browser",
            Color.rgb(0, 128, 0));

    /** Syntax color of modalities in the info tree (Swing {@code infotree.syntax.modality}). */
    public static final ColorSettingsF.ColorPropertyF INFOTREE_MODALITY =
        define("infotree.syntax.modality", "Modalities in the rule/symbol browser",
            Color.rgb(255, 175, 175));

    // ------------------------------------------------------------------
    // source view (Swing: sourceview/SourceView)
    // ------------------------------------------------------------------

    /** Background of symbolically executed lines (Swing {@code [SourceView]normalHighlight}). */
    public static final ColorSettingsF.ColorPropertyF SOURCE_NORMAL_HIGHLIGHT =
        define("[SourceView]normalHighlight",
            "Color for highlighting symbolically executed lines in source view",
            Color.rgb(194, 245, 194));

    /**
     * Background of the most recently executed line (Swing
     * {@code [SourceView]mostRecentHighlight}).
     */
    public static final ColorSettingsF.ColorPropertyF SOURCE_MOST_RECENT_HIGHLIGHT =
        define("[SourceView]mostRecentHighlight",
            "Color for highlighting most recently symbolically executed line in source view",
            Color.rgb(57, 210, 81));

    /** Background of source view tabs with highlights (Swing {@code [SourceView]tabHighlight}). */
    public static final ColorSettingsF.ColorPropertyF SOURCE_TAB_HIGHLIGHT =
        define("[SourceView]tabHighlight",
            "Color for highlighting source view tabs whose files contain highlighted lines",
            Color.rgb(57, 210, 81));

    /**
     * Background of the source of the selected term (Swing {@code [SourceView]originHighlight}).
     */
    public static final ColorSettingsF.ColorPropertyF SOURCE_ORIGIN_HIGHLIGHT =
        define("[SourceView]originHighlight",
            "Color for highlighting the origin of a selected term in source view",
            Color.rgb(252, 202, 80));

    // ------------------------------------------------------------------
    // .key problem files (Swing: sourceview/KeYEditorLexer)
    // ------------------------------------------------------------------

    /** Syntax color of keywords in .key files (Swing {@code [key]keyword}). */
    public static final ColorSettingsF.ColorPropertyF KEY_KEYWORD =
        define("[key]keyword", "Keyword in .key problem files", Color.rgb(0x7f, 0x00, 0x55));

    /** Syntax color of secondary keywords in .key files (Swing {@code [key]keyword2}). */
    public static final ColorSettingsF.ColorPropertyF KEY_KEYWORD2 =
        define("[key]keyword2", "Secondary keyword in .key problem files",
            Color.rgb(0x78, 0x52, 0x6C));

    /** Syntax color of comments in .key files (Swing {@code [key]comment}). */
    public static final ColorSettingsF.ColorPropertyF KEY_COMMENT =
        define("[key]comment", "Comment in .key problem files", Color.rgb(0x3f, 0x7f, 0x5f));

    /** Syntax color of literals in .key files (Swing {@code [key]literal}). */
    public static final ColorSettingsF.ColorPropertyF KEY_LITERAL =
        define("[key]literal", "Literal in .key problem files", Color.rgb(0x2A, 0x75, 0xB1));

    /** Syntax color of modalities in .key files (Swing {@code [key]modality}). */
    public static final ColorSettingsF.ColorPropertyF KEY_MODALITY =
        define("[key]modality", "Modality in .key problem files", Color.rgb(0xC6, 0x7C, 0x13));

    // ------------------------------------------------------------------
    // Java sources (Swing: sourceview/JavaDocument)
    // ------------------------------------------------------------------

    /** Java keyword color (Swing {@code [java]keyword}). */
    public static final ColorSettingsF.ColorPropertyF JAVA_KEYWORD =
        define("[java]keyword", "Keyword in Java source files", Color.rgb(0x7f, 0x00, 0x55),
            Color.rgb(0xCf, 0x50, 0xA5));

    /** Java comment color (Swing {@code [java]comment}). */
    public static final ColorSettingsF.ColorPropertyF JAVA_COMMENT =
        define("[java]comment", "Comment in Java source files", Color.rgb(0x3f, 0x7f, 0x5f),
            Color.rgb(0x9f, 0xBf, 0x9f));

    /** JavaDoc color (Swing {@code [java]javadoc}). */
    public static final ColorSettingsF.ColorPropertyF JAVA_JAVADOC =
        define("[java]javadoc", "Javadoc in Java source files", Color.rgb(0x3f, 0x7f, 0x5f),
            Color.rgb(0x9f, 0xBf, 0x9f));

    /** JML color (Swing {@code [java]jml}). */
    public static final ColorSettingsF.ColorPropertyF JAVA_JML =
        define("[java]jml", "JML annotation in Java source files", Color.rgb(0x00, 0x00, 0xc0),
            Color.rgb(0x88, 0x88, 0xcf));

    /** JML keyword color (Swing {@code [java]jmlKeyword}). */
    public static final ColorSettingsF.ColorPropertyF JAVA_JML_KEYWORD =
        define("[java]jmlKeyword", "JML keyword in Java source files", Color.rgb(0x00, 0x00, 0xf0),
            Color.rgb(0x88, 0x88, 0xcf));

    // ------------------------------------------------------------------
    // SMT solver listener (Swing: smt/SolverListener)
    // ------------------------------------------------------------------

    /** Color of failing SMT solver tasks (Swing {@code [solverListener]red}). */
    public static final ColorSettingsF.ColorPropertyF SMT_RED =
        define("[solverListener]red", "Failing SMT solver task", Color.rgb(180, 43, 43));

    /** Color of succeeding SMT solver tasks (Swing {@code [solverListener]green}). */
    public static final ColorSettingsF.ColorPropertyF SMT_GREEN =
        define("[solverListener]green", "Succeeding SMT solver task", Color.rgb(43, 180, 43));

    // ------------------------------------------------------------------
    // settings dialog (Swing: settings/SimpleSettingsPanel)
    // ------------------------------------------------------------------

    /**
     * Error color of erroneous settings text fields (Swing
     * {@code SETTINGS_TEXTFIELD_ERROR}). Also referenced by
     * {@code SettingsPanelF.COLOR_ERROR}; {@code createColorProperty} is idempotent, so both
     * names denote the same property.
     */
    public static final ColorSettingsF.ColorPropertyF SETTINGS_ERROR =
        define("SETTINGS_TEXTFIELD_ERROR",
            "Color for marking erroneous text fields in the settings dialog",
            Color.rgb(200, 100, 100));

    // ------------------------------------------------------------------
    // search bar (Swing: SearchBar)
    // ------------------------------------------------------------------

    /** Alert color of the proof tree search bar (Swing {@code [searchBar]alert}). */
    public static final ColorSettingsF.ColorPropertyF SEARCH_ALERT =
        define("[searchBar]alert", "Alert color of the search bar", Color.rgb(255, 178, 178),
            Color.rgb(85, 40, 40));

    // ------------------------------------------------------------------
    // proof tree (Swing: prooftree/ProofTreeView)
    // ------------------------------------------------------------------

    /** Color of merged goals in the proof tree (Swing {@code [proofTree]gray}). */
    public static final ColorSettingsF.ColorPropertyF PROOF_TREE_GRAY =
        define("[proofTree]gray", "Color of merged goals in the proof tree",
            Color.rgb(0x40, 0x40, 0x40), Color.rgb(0xc0, 0xc0, 0xc0));

    /** Color of linked goals in the proof tree (Swing {@code [proofTree]lightBlue}). */
    public static final ColorSettingsF.ColorPropertyF PROOF_TREE_LIGHT_BLUE =
        define("[proofTree]lightBlue", "Color of linked goals in the proof tree",
            Color.rgb(230, 254, 255));

    /** Color of closed goals in the proof tree (Swing {@code [proofTree]darkGreen}). */
    public static final ColorSettingsF.ColorPropertyF PROOF_TREE_DARK_GREEN =
        define("[proofTree]darkGreen", "Color of closed goals in the proof tree",
            Color.rgb(0, 128, 51), Color.rgb(100, 255, 102));

    /** Color of open goals in the proof tree (Swing {@code [proofTree]darkRed}). */
    public static final ColorSettingsF.ColorPropertyF PROOF_TREE_DARK_RED =
        define("[proofTree]darkRed", "Color of open goals in the proof tree", Color.rgb(191, 0, 0),
            Color.rgb(191, 120, 120));

    /** Color of interactive goals in the proof tree (Swing {@code [proofTree]pink}). */
    public static final ColorSettingsF.ColorPropertyF PROOF_TREE_PINK =
        define("[proofTree]pink", "Color of interactive goals in the proof tree",
            Color.rgb(255, 0, 240));

    /** Color of automated goals in the proof tree (Swing {@code [proofTree]orange}). */
    public static final ColorSettingsF.ColorPropertyF PROOF_TREE_ORANGE =
        define("[proofTree]orange", "Color of automated goals in the proof tree",
            Color.rgb(255, 140, 0), Color.rgb(255, 180, 40));

    // ------------------------------------------------------------------
    // javac extension (Swing: plugins/javac/JavacExtension)
    // ------------------------------------------------------------------

    /** Color of javac fine messages (Swing {@code javac.fine}). */
    public static final ColorSettingsF.ColorPropertyF JAVAC_FINE =
        define("javac.fine", "Javac fine message", Color.rgb(80, 120, 200));

    /** Color of javac error messages (Swing {@code javac.error}). */
    public static final ColorSettingsF.ColorPropertyF JAVAC_ERROR =
        define("javac.error", "Javac error message", Color.rgb(200, 20, 80));

    /** Color of javac warning messages (Swing {@code javac.warn}). */
    public static final ColorSettingsF.ColorPropertyF JAVAC_WARN =
        define("javac.warn", "Javac warning message", Color.rgb(200, 120, 80));

    // ------------------------------------------------------------------
    // sequent search bar (Swing: nodeviews/SequentViewSearchBar)
    // ------------------------------------------------------------------

    /**
     * Highlight color 1 of the sequent search bar (Swing {@code [sequentSearchBar]highlight_1}).
     */
    public static final ColorSettingsF.ColorPropertyF SEQUENT_SEARCH_HIGHLIGHT_1 =
        define("[sequentSearchBar]highlight_1", "Sequent search highlight (first match)",
            Color.rgb(0, 140, 255, 178 / 255.0));

    /**
     * Highlight color 2 of the sequent search bar (Swing {@code [sequentSearchBar]highlight_2}).
     */
    public static final ColorSettingsF.ColorPropertyF SEQUENT_SEARCH_HIGHLIGHT_2 =
        define("[sequentSearchBar]highlight_2", "Sequent search highlight (other matches)",
            Color.rgb(0, 140, 255, 100 / 255.0));

    // ------------------------------------------------------------------
    // sequent view (Swing: nodeviews/SequentView, SequentViewInputListener)
    // ------------------------------------------------------------------

    /**
     * Color of the mouse selection in the sequent (Swing {@code [currentGoal]mouseSelectionColor}).
     */
    public static final ColorSettingsF.ColorPropertyF CURRENT_GOAL_MOUSE_SELECTION =
        define("[currentGoal]mouseSelectionColor",
            "Color of the mouse selection in the sequent view", Color.rgb(230, 230, 230, 1.0));

    /** Color of permanent highlights in the sequent (Swing {@code [currentGoal]permaHighlight}). */
    public static final ColorSettingsF.ColorPropertyF CURRENT_GOAL_PERMA_HIGHLIGHT =
        define("[currentGoal]permaHighlight", "Permanent highlight in the sequent view",
            Color.rgb(110, 85, 181, 76 / 255.0), Color.rgb(210, 185, 201, 200 / 255.0));

    /**
     * Color of the default highlight in the sequent (Swing {@code [currentGoal]defaultHighlight}).
     */
    public static final ColorSettingsF.ColorPropertyF CURRENT_GOAL_DEFAULT_HIGHLIGHT =
        define("[currentGoal]defaultHighlight", "Default highlight in the sequent view",
            Color.rgb(70, 100, 170, 76 / 255.0), Color.rgb(140, 200, 255, 180 / 255.0));

    /**
     * Color of additional highlights in the sequent (Swing
     * {@code [currentGoal]addtionalHighlight}).
     */
    public static final ColorSettingsF.ColorPropertyF CURRENT_GOAL_ADDTIONAL_HIGHLIGHT =
        define("[currentGoal]addtionalHighlight", "Additional highlight in the sequent view",
            Color.rgb(0, 0, 0, 38 / 255.0), Color.rgb(240, 220, 255, 180 / 255.0));

    /** Color of update highlights in the sequent (Swing {@code [currentGoal]updateHighlight}). */
    public static final ColorSettingsF.ColorPropertyF CURRENT_GOAL_UPDATE_HIGHLIGHT =
        define("[currentGoal]updateHighlight", "Update highlight in the sequent view",
            Color.rgb(0, 150, 130, 38 / 255.0), Color.rgb(0, 150, 130, 1.0));

    /**
     * Color of drag and drop highlights in the sequent (Swing {@code [currentGoal]dndHighlight}).
     */
    public static final ColorSettingsF.ColorPropertyF CURRENT_GOAL_DND_HIGHLIGHT =
        define("[currentGoal]dndHighlight", "Drag and drop highlight in the sequent view",
            Color.rgb(0, 150, 130, 1.0));

    /** Base color of the heatmap overlay (Swing {@code [Heatmap]basecolor}). */
    public static final ColorSettingsF.ColorPropertyF HEATMAP_BASE_COLOR =
        define("[Heatmap]basecolor", "Base color of the heatmap overlay", Color.rgb(252, 202, 80));

    /**
     * Alert color of the sequent hide-warning border (Swing
     * {@code [sequentHideWarningBorder]alert}).
     */
    public static final ColorSettingsF.ColorPropertyF SEQUENT_HIDE_WARNING_ALERT =
        define("[sequentHideWarningBorder]alert", "Alert color of the hide-warning border",
            Color.rgb(255, 178, 178));

    // ------------------------------------------------------------------
    // inner node view (Swing: nodeviews/InnerNodeView)
    // ------------------------------------------------------------------

    /** Highlight color of rule applications (Swing {@code [innerNodeView]ruleAppHighlight}). */
    public static final ColorSettingsF.ColorPropertyF INNER_NODE_RULE_APP_HIGHLIGHT =
        define("[innerNodeView]ruleAppHighlight",
            "Rule application highlight in the inner node view",
            new Color(0.5, 1.0, 0.5, 0.4));

    /** Highlight color of if-formulas (Swing {@code [innerNodeView]ifFormulaHighlight}). */
    public static final ColorSettingsF.ColorPropertyF INNER_NODE_IF_FORMULA_HIGHLIGHT =
        define("[innerNodeView]ifFormulaHighlight",
            "If-formula highlight in the inner node view", new Color(0.8, 1.0, 0.8, 0.5));

    /** Selection color of the inner node view (Swing {@code [innerNodeView]selection}). */
    public static final ColorSettingsF.ColorPropertyF INNER_NODE_SELECTION =
        define("[innerNodeView]selection", "Selection in the inner node view",
            Color.rgb(10, 180, 50));

    // ------------------------------------------------------------------
    // sequent syntax highlighting (Swing: nodeviews/HTMLSyntaxHighlighter)
    // ------------------------------------------------------------------

    /**
     * Color of propositional logic in the sequent (Swing {@code [sequentView]prop_logic_color}).
     */
    public static final ColorSettingsF.ColorPropertyF SEQUENT_PROP_LOGIC =
        define("[sequentView]prop_logic_color", "Propositional logic in the sequent view",
            Color.rgb(0, 0, 0), Color.rgb(255, 255, 255));

    /** Color of dynamic logic in the sequent (Swing {@code [sequentView]dyn_logic_color}). */
    public static final ColorSettingsF.ColorPropertyF SEQUENT_DYN_LOGIC =
        define("[sequentView]dyn_logic_color", "Dynamic logic in the sequent view",
            Color.rgb(0, 0, 16 * 13), Color.rgb(150, 150, 250));

    /** Color of program variables in the sequent (Swing {@code [sequentView]prog_var_color}). */
    public static final ColorSettingsF.ColorPropertyF SEQUENT_PROG_VAR =
        define("[sequentView]prog_var_color", "Program variables in the sequent view",
            Color.rgb(0x6A, 0x3E, 0x3E), Color.rgb(100, 100, 250));

    /** Color of sequent arrows in the sequent (Swing {@code [sequentView]sequent_arrow_color}). */
    public static final ColorSettingsF.ColorPropertyF SEQUENT_ARROW =
        define("[sequentView]sequent_arrow_color", "Sequent arrow in the sequent view",
            Color.rgb(0x6A, 0x3E, 0x3E), Color.rgb(100, 100, 250));

    /**
     * Registers the property in {@link ColorSettingsF}; re-uses an existing definition of the
     * same key (the settings file may already contain an entry of a foreign or older UI).
     *
     * @param key the key in {@code colors.json}
     * @param desc a human readable description
     * @param light the light theme default
     * @param dark the dark theme default
     * @return the registered property
     */
    private static ColorSettingsF.ColorPropertyF define(String key, String desc, Color light,
            Color dark) {
        return ColorSettingsF.define(key, desc, light, dark);
    }

    /**
     * Registers the property with the same default for both themes.
     *
     * @param key the key in {@code colors.json}
     * @param desc a human readable description
     * @param color the default
     * @return the registered property
     */
    private static ColorSettingsF.ColorPropertyF define(String key, String desc, Color color) {
        return ColorSettingsF.define(key, desc, color);
    }
}
