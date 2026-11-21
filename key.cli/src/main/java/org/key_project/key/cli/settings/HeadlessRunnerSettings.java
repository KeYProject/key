/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.settings;

import java.nio.file.Path;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.settings.ProofSettings;

import org.jspecify.annotations.Nullable;

/**
 * Assembles the per-run strategy choices of the headless CLI (§5.1 of the headless interface spec)
 * and applies them for the duration of a proof run.
 * <p>
 * The sources are layered in order of precedence (high to low): {@code --strategy-option} entries
 * override {@code --settings-file} entries on a per-key basis ({@link #layer}), and both are only
 * applied for keys the caller actually named, leaving the remaining choices at their load-file/KeY
 * defaults (which KeY computes during problem-load via {@code InitConfig.computeDefaults}).
 * <p>
 * KeY's {@link ChoiceSettings} is a mutable global ({@link ProofSettings#DEFAULT_SETTINGS}): choice
 * state changed here is visible to the ongoing proof run but outlives it. {@link #apply()}
 * therefore
 * captures the previous default choices and {@link #close()} restores them, so a run leaves the
 * global choices exactly as it found them (the canonical capture/restore pattern used throughout
 * KeY — cf. {@code HelperClassForTests.restoreTacletOptions}).
 * <p>
 * Values are checked twice: {@link SettingsFileParser} accepts only the documented vocabulary, and
 * {@link #validate()} (called after the problem is loaded) rejects any value the loaded KeY does
 * not declare, so the silent substitution KeY performs for unknown choice names cannot hide a
 * typo (§5.3). The historical {@code intRules:checked}/{@code intRules:unchecked} and
 * {@code methodExpansion:full} shorthands are normalized to the real KeY choice names.
 */
public final class HeadlessRunnerSettings implements AutoCloseable {

    private final Map<String, String> choices;

    private @org.jspecify.annotations.Nullable Map<String, String> previousChoices;

    private boolean applied;

    private HeadlessRunnerSettings(Map<String, String> choices) {
        this.choices = choices;
    }

    /**
     * Creates the run settings for a {@code --settings-file} and the given
     * {@code --strategy-option <KEY>=<VALUE>} entries.
     * <p>
     * The settings file is parsed and validated by {@link SettingsFileParser}; the strategy options
     * use the same §5.2 vocabulary and are layered on top of the file, so an option wins over the
     * file for its key. No choice is applied to KeY until {@link #apply()} is called, and the keys
     * not named by either source are left untouched.
     *
     * @param settingsFile the {@code --settings-file} path, or {@code null} if none was given
     * @param strategyOptions the {@code --strategy-option} entries in command-line order
     * @return the assembled run settings (not yet applied)
     * @throws CliSettingsException if the settings file or a strategy option is not understood
     */
    public static HeadlessRunnerSettings from(@Nullable Path settingsFile,
            List<String> strategyOptions) throws CliSettingsException {
        SettingsFileParser parser = new SettingsFileParser();
        Map<String, String> file = settingsFile != null ? parser.parse(settingsFile) : Map.of();
        return new HeadlessRunnerSettings(layer(file, strategyOptions));
    }

    /**
     * Layers the {@code --strategy-option} entries over a settings-file map (§5.1 precedence: an
     * option wins per key) and normalizes the §5.2 shorthand values to their real KeY choice names.
     * <p>
     * The returned map is keyed by choice category and maps to the full choice name KeY expects in
     * {@link ChoiceSettings#setDefaultChoices(Map)}. It is derived from the settings-file map with
     * each {@code <KEY>=<VALUE>} option validated against the §5.2 vocabulary and overriding the
     * file (or introducing the key) for its category. Keys not named by either source are absent,
     * so
     * they fall back to the load-file/{@code computeDefaults} defaults.
     *
     * @param settingsFile the parsed settings-file map (category to documented value), possibly
     *        empty
     * @param strategyOptions the {@code --strategy-option} entries in command-line order
     * @return the layered, normalized map (category to actual choice name)
     * @throws CliSettingsException if a strategy option is not a documented key/value
     */
    public static Map<String, String> layer(Map<String, String> settingsFile,
            List<String> strategyOptions) throws CliSettingsException {
        Map<String, String> merged = new HashMap<>();
        for (Map.Entry<String, String> entry : settingsFile.entrySet()) {
            merged.put(entry.getKey(), normalize(entry.getKey(), entry.getValue()));
        }
        for (String option : strategyOptions) {
            int eq = option.indexOf('=');
            if (eq <= 0 || eq == option.length() - 1) {
                throw new CliSettingsException("settings: '" + option + "' not understood");
            }
            String key = option.substring(0, eq);
            String value = option.substring(eq + 1);
            SettingsFileParser.validateStrategyOption(key, value);
            merged.put(key, normalize(key, value));
        }
        return Map.copyOf(merged);
    }

    /**
     * Applies the assembled choices to KeY's default choice settings, capturing the previous
     * choices so {@link #close()} can restore them. Calling this again is a no-op once applied.
     */
    public void apply() {
        if (applied) {
            return;
        }
        ChoiceSettings cs = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
        previousChoices = new HashMap<>(cs.getDefaultChoices());
        Map<String, String> newChoices = new HashMap<>(previousChoices);
        newChoices.putAll(choices);
        cs.setDefaultChoices(newChoices);
        applied = true;
    }

    /**
     * Restores the default choices that were in effect before {@link #apply()}. Harmless when the
     * settings were never applied.
     */
    @Override
    public void close() {
        if (!applied) {
            return;
        }
        ChoiceSettings cs = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
        Map<String, String> previous = previousChoices;
        cs.setDefaultChoices(new HashMap<>(previous != null ? previous : Map.of()));
        applied = false;
    }

    /**
     * Returns the actual per-category choice names this run will apply, for tests and diagnostics.
     *
     * @return an unmodifiable copy of the assembled choices
     */
    public Map<String, String> choices() {
        return Map.copyOf(choices);
    }

    /**
     * Normalizes the retained historical shorthands to the real KeY choice names: the documented
     * {@code intRules:checked}/{@code intRules:unchecked} and {@code methodExpansion:full} are
     * mapped to the names KeY 3 declares; every other accepted value is already a declared choice
     * name and is passed through unchanged.
     *
     * @param category the §5.2 choice category
     * @param value the accepted §5.2 value
     * @return the actual choice name KeY understands
     */
    static String normalize(String category, String value) {
        if ("intRules".equals(category)) {
            return switch (value) {
                case "intRules:checked" -> "intRules:arithmeticSemanticsCheckingOF";
                case "intRules:unchecked" -> "intRules:arithmeticSemanticsIgnoringOF";
                default -> value;
            };
        }
        if ("methodExpansion".equals(category) && "methodExpansion:full".equals(value)) {
            return "methodExpansion:noRestriction";
        }
        return value;
    }

    /**
     * Verifies that every requested choice is declared by the loaded environment, so a value KeY
     * would otherwise substitute silently becomes an input error (§5.3). Must be called after the
     * problem is loaded (the declared choices come from the loaded rule declarations).
     *
     * @throws CliSettingsException if a requested {@code category:value} is not declared
     */
    public void validate() throws CliSettingsException {
        validate(ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().getChoices());
    }

    /**
     * Verifies the requested choices against the given declared choices.
     *
     * @param declared the declared choice names per category (from
     *        {@link ChoiceSettings#getChoices()})
     * @throws CliSettingsException if a requested {@code category:value} is not declared
     */
    void validate(Map<String, Set<String>> declared) throws CliSettingsException {
        for (Map.Entry<String, String> entry : choices.entrySet()) {
            String category = entry.getKey();
            String full = entry.getValue();
            Set<String> values = declared.get(category);
            if (values == null || !values.contains(full)) {
                throw new CliSettingsException("settings: '" + full + "' not understood for '"
                    + category + "'; declared values: " + declaredHint(values));
            }
        }
    }

    private static String declaredHint(@Nullable Set<String> values) {
        if (values == null || values.isEmpty()) {
            return "(no such choice category in this KeY version)";
        }
        return values.stream().sorted().collect(Collectors.joining(", "));
    }
}
