/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.keyshortcuts;

import java.io.IOException;
import java.io.Writer;
import java.lang.ref.WeakReference;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Optional;
import java.util.TreeMap;
import javafx.scene.control.MenuItem;
import javafx.scene.input.KeyCode;
import javafx.scene.input.KeyCodeCombination;
import javafx.scene.input.KeyCombination;
import javafx.scene.input.KeyCombination.ModifierValue;

import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.settings.PathConfig;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Central registry of keyboard shortcuts of the JavaFX UI, counter-part of
 * {@code KeyStrokeManager}/{@code KeyStrokeSettings} of the Swing module {@code key.ui}.
 * <p>
 * Actions are keyed by the fully qualified class name of their Swing counterpart, so the
 * persisted {@code keystrokes.json} is shared with the Swing UI: the file is read at startup
 * (user overrides of the registered actions win, exactly like the Swing
 * {@code KeyStrokeSettings} constructor merges the file over the defaults; an empty file value
 * falls back to the default) and written back in the same format on every rebind and on exit.
 * <p>
 * The persisted format is the Swing {@code KeyStroke.toString()} format, e.g.
 * {@code "shift ctrl pressed P"}; {@link #fromSwingSpec(String)} and {@link #toSwingSpec(
 * KeyCombination)} convert to/from JavaFX {@link KeyCombination}s. Entries of actions unknown to
 * this UI are preserved verbatim on save.
 */
public final class KeyStrokeManagerF {

    private static final Logger LOGGER = LoggerFactory.getLogger(KeyStrokeManagerF.class);

    /** the shared shortcut file (the same as the Swing module's) */
    public static final Path SETTINGS_FILE = PathConfig.getSettingsFile("keystrokes.json");

    /**
     * shortcuts (P1): the former (pre Swing-parity) FX defaults of the re-mapped actions, in the
     * shared Swing spec format. A persisted entry equal to one of these is treated as "not
     * customized" on load, so a {@code keystrokes.json} written by an earlier FX version (which
     * persists the full binding table on exit) heals to the new defaults instead of keeping the
     * stale ones. A genuine user customization that coincides with an old default is re-defaulted
     * with it (indistinguishable from the stale entry). Declared before the singleton field:
     * {@link #load()} runs from the constructor during class initialization.
     */
    private static final Map<String, String> LEGACY_DEFAULTS = createLegacyDefaults();

    private static final boolean MAC =
        System.getProperty("os.name", "").toLowerCase(Locale.ROOT).contains("mac");

    private static final KeyStrokeManagerF INSTANCE = new KeyStrokeManagerF();

    private final Map<String, KeyCombination> bindings = new TreeMap<>();

    /** file entries of actions this UI does not know; preserved on save */
    private final Map<String, String> persistedEntries = new TreeMap<>();

    /**
     * Menu items registered per action id (weakly, like the Swing
     * {@code KeyStrokeManager.actions} registry); their accelerators are updated on rebinding.
     */
    private final Map<String, List<WeakReference<MenuItem>>> registeredItems = new HashMap<>();

    private KeyStrokeManagerF() {
        registerDefaults();
        load();
        Runtime.getRuntime().addShutdownHook(new Thread(this::save));
    }

    /**
     * @return the global shortcut manager instance
     */
    public static KeyStrokeManagerF getInstance() {
        return INSTANCE;
    }

    private void registerDefaults() {
        // shortcuts (P1): Swing-parity defaults — macros and the search/toggle actions use
        // CTRL+SHIFT (KeyStrokeSettings.java:44 "use CTRL+SHIFT+letter for macros", :60-76), so
        // the former FX defaults without the Shift modifier no longer collide with the
        // Ctrl+SPACE auto mode and the Ctrl+C term copy
        defineDefault("de.uka.ilkd.key.macros.FullAutoPilotProofMacro", modifier() + "SHIFT+V");
        defineDefault("de.uka.ilkd.key.macros.AutoPilotPrepareProofMacro", modifier() + "SHIFT+D");
        defineDefault("de.uka.ilkd.key.macros.PropositionalExpansionMacro", modifier() + "SHIFT+A");
        defineDefault("de.uka.ilkd.key.macros.FullPropositionalExpansionMacro",
            modifier() + "SHIFT+S");
        defineDefault("de.uka.ilkd.key.macros.TryCloseMacro", modifier() + "SHIFT+C");
        defineDefault("de.uka.ilkd.key.macros.FinishSymbolicExecutionMacro",
            modifier() + "SHIFT+X");
        defineDefault("de.uka.ilkd.key.macros.OneStepProofMacro", modifier() + "SHIFT+SPACE");
        defineDefault("de.uka.ilkd.key.macros.HeapSimplificationMacro", modifier() + "SHIFT+H");
        defineDefault("de.uka.ilkd.key.macros.UpdateSimplificationMacro", modifier() + "SHIFT+L");
        defineDefault("de.uka.ilkd.key.macros.IntegerSimplificationMacro", modifier() + "SHIFT+I");
        defineDefault("de.uka.ilkd.key.macros.SMTPreparationMacro", modifier() + "SHIFT+Y");

        defineDefault("de.uka.ilkd.key.gui.actions.SearchInProofTreeAction",
            modifier() + "SHIFT+F");
        defineDefault("de.uka.ilkd.key.gui.actions.PrettyPrintToggleAction",
            modifier() + "SHIFT+P");
        defineDefault("de.uka.ilkd.key.gui.actions.UnicodeToggleAction", modifier() + "SHIFT+U");
        defineDefault("de.uka.ilkd.key.gui.actions.ProofManagementAction", modifier() + "SHIFT+M");

        defineDefault("de.uka.ilkd.key.gui.actions.QuickSaveAction", "F5");
        defineDefault("de.uka.ilkd.key.gui.actions.QuickLoadAction", "F6");

        // docking layout slots (Swing DockingLayout: the save actions use the shortcut mask +
        // SHIFT (Ctrl+Shift+F10..F12), the load actions the shortcut mask (Ctrl+F10..F12))
        defineDefault("de.uka.ilkd.key.gui.docking.SaveLayoutAction$Default",
            modifier() + "SHIFT+F10");
        defineDefault("de.uka.ilkd.key.gui.docking.SaveLayoutAction$Slot 1",
            modifier() + "SHIFT+F11");
        defineDefault("de.uka.ilkd.key.gui.docking.SaveLayoutAction$Slot 2",
            modifier() + "SHIFT+F12");
        defineDefault("de.uka.ilkd.key.gui.docking.LoadLayoutAction$Default", modifier() + "F10");
        defineDefault("de.uka.ilkd.key.gui.docking.LoadLayoutAction$Slot 1", modifier() + "F11");
        defineDefault("de.uka.ilkd.key.gui.docking.LoadLayoutAction$Slot 2", modifier() + "F12");

        defineDefault("de.uka.ilkd.key.gui.actions.IncreaseFontSizeAction", modifier() + "PLUS");
        defineDefault("de.uka.ilkd.key.gui.actions.DecreaseFontSizeAction", modifier() + "MINUS");
        defineDefault("de.uka.ilkd.key.gui.actions.AbandonTaskAction", modifier() + "W");
        defineDefault("de.uka.ilkd.key.gui.actions.PruneProofAction", modifier() + "DELETE");
        defineDefault("de.uka.ilkd.key.gui.actions.GoalBackAction", modifier() + "Z");
        defineDefault("de.uka.ilkd.key.gui.actions.CopyToClipboardAction", modifier() + "C");
        defineDefault("de.uka.ilkd.key.gui.actions.ExitMainAction", modifier() + "Q");
        defineDefault("de.uka.ilkd.key.gui.actions.GoalSelectAboveAction", modifier() + "K");
        defineDefault("de.uka.ilkd.key.gui.actions.GoalSelectBelowAction", modifier() + "J");
        defineDefault("de.uka.ilkd.key.gui.actions.AutoModeAction", modifier() + "SPACE");
        defineDefault("de.uka.ilkd.key.gui.actions.OpenMostRecentFileAction", modifier() + "R");
        defineDefault("de.uka.ilkd.key.gui.actions.SaveBundleAction", modifier() + "B");
        defineDefault("de.uka.ilkd.key.gui.actions.SaveFileAction", modifier() + "S");
        defineDefault("de.uka.ilkd.key.gui.settings.SettingsManager$ShowSettingsAction",
            modifier() + "N");
        defineDefault("de.uka.ilkd.key.gui.actions.OpenFileAction", modifier() + "O");
        // sequent search is Ctrl+F in Swing (KeyStrokeSettings.java:102
        // SearchInSequentAction.java:15 "Keyboard shortcut: STRG+F"); the former FX default was
        // the bare F, which hijacked typing F anywhere
        defineDefault("de.uka.ilkd.key.gui.actions.SearchInSequentAction", modifier() + "F");
        defineDefault("de.uka.ilkd.key.gui.actions.SearchNextAction", "F3");
        defineDefault("de.uka.ilkd.key.gui.actions.SearchPreviousAction", "SHIFT+F3");
        defineDefault("de.uka.ilkd.key.gui.actions.SelectionBackAction", "SHORTCUT+ALT+LEFT");
        defineDefault("de.uka.ilkd.key.gui.actions.SelectionForwardAction", "SHORTCUT+ALT+RIGHT");
    }

    /**
     * shortcuts (P1): the former (pre Swing-parity) FX defaults of the re-mapped actions, in the
     * shared Swing spec format. See {@link #LEGACY_DEFAULTS} (declared before the singleton
     * field) for the rationale.
     */
    private static Map<String, String> createLegacyDefaults() {
        String[][] changed = {
            { "de.uka.ilkd.key.macros.FullAutoPilotProofMacro", "V" },
            { "de.uka.ilkd.key.macros.AutoPilotPrepareProofMacro", "D" },
            { "de.uka.ilkd.key.macros.PropositionalExpansionMacro", "A" },
            { "de.uka.ilkd.key.macros.FullPropositionalExpansionMacro", "S" },
            { "de.uka.ilkd.key.macros.TryCloseMacro", "C" },
            { "de.uka.ilkd.key.macros.FinishSymbolicExecutionMacro", "X" },
            { "de.uka.ilkd.key.macros.OneStepProofMacro", "SPACE" },
            { "de.uka.ilkd.key.macros.HeapSimplificationMacro", "H" },
            { "de.uka.ilkd.key.macros.UpdateSimplificationMacro", "L" },
            { "de.uka.ilkd.key.macros.IntegerSimplificationMacro", "I" },
            { "de.uka.ilkd.key.macros.SMTPreparationMacro", "Y" },
            { "de.uka.ilkd.key.gui.actions.PrettyPrintToggleAction", "P" },
            { "de.uka.ilkd.key.gui.actions.UnicodeToggleAction", "U" },
            { "de.uka.ilkd.key.gui.actions.ProofManagementAction", "M" },
            { "de.uka.ilkd.key.gui.actions.SearchInProofTreeAction", "F" } };
        Map<String, String> legacy = new HashMap<>();
        for (String[] entry : changed) {
            legacy.put(entry[0], "ctrl pressed " + entry[1]);
        }
        legacy.put("de.uka.ilkd.key.gui.actions.SearchInSequentAction", "pressed F");
        return legacy;
    }

    private static String modifier() {
        return "SHORTCUT+";
    }

    private static KeyCombination combo(String spec) {
        return KeyCombination.keyCombination(spec);
    }

    private void defineDefault(String actionId, String spec) {
        bindings.put(actionId, combo(spec));
    }

    /**
     * @return the registered shortcut for the given action, if any
     */
    public Optional<KeyCombination> binding(String actionId) {
        return Optional.ofNullable(bindings.get(actionId));
    }

    /**
     * @return all known action ids with their current bindings
     */
    public Map<String, KeyCombination> getBindings() {
        return Map.copyOf(bindings);
    }

    /**
     * @return the file entries of actions unknown to this UI (they are shown in the shortcut
     *         table without a description and preserved on save)
     */
    public Map<String, String> getPersistedEntries() {
        return Map.copyOf(persistedEntries);
    }

    /**
     * @return a short description of the action with the given id, taken from the text of a
     *         registered menu item (the FX equivalent of the Swing
     *         {@code Action.SHORT_DESCRIPTION})
     */
    public Optional<String> descriptionOf(String actionId) {
        List<WeakReference<MenuItem>> items = registeredItems.get(actionId);
        if (items == null) {
            return Optional.empty();
        }
        items.removeIf(ref -> ref.get() == null);
        return items.stream().map(WeakReference::get).filter(java.util.Objects::nonNull)
                .map(MenuItem::getText).filter(java.util.Objects::nonNull).findFirst();
    }

    /**
     * Binds a shortcut to an action, overriding a possible default, updates the accelerators of
     * the registered menu items and persists the change.
     *
     * @param actionId the action id
     * @param combination the shortcut, or {@code null} to remove the binding (the default
     *        returns on the next start, mirroring the Swing handling of empty file entries)
     */
    public void bind(String actionId, KeyCombination combination) {
        if (combination == null) {
            bindings.remove(actionId);
        } else {
            bindings.put(actionId, combination);
        }
        rebind(actionId);
        save();
    }

    /**
     * Clears all overrides and re-establishes the default shortcuts (persisted).
     */
    public void resetToDefaults() {
        bindings.clear();
        registerDefaults();
        rebindAll();
        save();
    }

    /**
     * Registers a menu item for the given action id so that its accelerator follows later
     * rebindings (Swing {@code KeyStrokeManager.registerAction}).
     *
     * @param item the menu item carrying the accelerator
     * @param actionId the action id
     */
    public void register(MenuItem item, String actionId) {
        registeredItems.computeIfAbsent(actionId, key -> new ArrayList<>())
                .add(new WeakReference<>(item));
    }

    /**
     * Updates the accelerators of all registered menu items (Swing sets the accelerator on the
     * registered actions).
     */
    public void rebindAll() {
        bindings.keySet().forEach(this::rebind);
    }

    private void rebind(String actionId) {
        KeyCombination combination = bindings.get(actionId);
        List<WeakReference<MenuItem>> items = registeredItems.get(actionId);
        if (items == null) {
            return;
        }
        items.removeIf(ref -> ref.get() == null);
        for (WeakReference<MenuItem> ref : items) {
            MenuItem item = ref.get();
            if (item != null) {
                item.setAccelerator(combination);
            }
        }
    }

    /**
     * @return an immutable snapshot of the current bindings (action id → shortcut spec in the
     *         shared Swing file format), ready for persistence
     */
    public Map<String, String> snapshot() {
        TreeMap<String, String> copy = new TreeMap<>();
        bindings.forEach((id, keyCombination) -> copy.put(id, toSwingSpec(keyCombination)));
        return copy;
    }

    // ------------------------------------------------------------------
    // persistence (keystrokes.json, shared with the Swing UI)
    // ------------------------------------------------------------------

    /**
     * Reads {@link #SETTINGS_FILE}: entries of the registered actions override the defaults
     * (empty entries fall back to the default, Swing parity), unknown entries are preserved for
     * the write-back.
     */
    private void load() {
        if (!Files.exists(SETTINGS_FILE)) {
            return;
        }
        try {
            LOGGER.info("Load keyboard shortcuts from {}", SETTINGS_FILE);
            Configuration.load(SETTINGS_FILE).getEntries().forEach(entry -> {
                String value = entry.getValue() == null ? "" : entry.getValue().toString();
                Optional<KeyCombination> combination = fromSwingSpec(value);
                if (bindings.containsKey(entry.getKey())) {
                    // a stale persisted entry that equals a former FX default heals to the new
                    // (Swing-parity) default; an empty entry falls back to the default, like the
                    // Swing constructor
                    boolean legacy = combination.isPresent() && combination.get()
                            .equals(fromSwingSpec(LEGACY_DEFAULTS.get(entry.getKey()))
                                    .orElse(null));
                    if (!legacy) {
                        combination
                                .ifPresent(keyCombination -> bindings.put(entry.getKey(),
                                    keyCombination));
                    } else {
                        LOGGER.info("Re-defaulting the stale entry {} = {}", entry.getKey(), value);
                    }
                } else {
                    persistedEntries.put(entry.getKey(), value);
                }
            });
        } catch (IOException e) {
            LOGGER.error("Could not read {}", SETTINGS_FILE, e);
        }
    }

    /**
     * Writes the bindings and the preserved unknown entries back to {@link #SETTINGS_FILE} in
     * the shared Swing format (Swing {@code KeyStrokeSettings.save}).
     */
    public void save() {
        try {
            Files.createDirectories(SETTINGS_FILE.getParent());
            LOGGER.info("Save keyboard shortcuts to: {}", SETTINGS_FILE.toAbsolutePath());
            TreeMap<String, Object> merged = new TreeMap<>(persistedEntries);
            merged.putAll(snapshot());
            try (Writer writer = Files.newBufferedWriter(SETTINGS_FILE)) {
                var config = new Configuration(merged);
                config.save(writer, "KeY's KeyStrokes");
                writer.flush();
            }
        } catch (IOException ex) {
            LOGGER.warn("Failed to save keyboard shortcuts", ex);
        }
    }

    // ------------------------------------------------------------------
    // conversion of the shared Swing KeyStroke format
    // ------------------------------------------------------------------

    /**
     * Parses a Swing {@code KeyStroke.toString()} spec into a {@link KeyCombination}. The
     * supported forms are {@code [modifier]* [pressed|released|typed] KEY} with the modifiers
     * {@code shift ctrl meta alt altGraph} and mouse {@code button*} modifiers (ignored, mouse
     * chords are not representable). {@code typed} keystrokes become the plain key without
     * modifiers (JavaFX has no typed-key combinations) — not produced by the default sets.
     *
     * @param spec the spec, may be null or empty
     * @return the combination, or empty for null/empty/unparseable specs
     */
    public static Optional<KeyCombination> fromSwingSpec(String spec) {
        if (spec == null || spec.isBlank()) {
            return Optional.empty();
        }
        // Swing KeyStroke semantics: a modifier not mentioned in the spec must be UP (a Swing
        // "ctrl pressed F11" stroke does not match an event with shift also pressed)
        ModifierValue shift = ModifierValue.UP;
        ModifierValue ctrl = ModifierValue.UP;
        ModifierValue meta = ModifierValue.UP;
        ModifierValue alt = ModifierValue.UP;
        String key = null;
        for (String token : spec.trim().split("\\s+")) {
            switch (token) {
                case "shift" -> shift = ModifierValue.DOWN;
                case "ctrl" -> ctrl = ModifierValue.DOWN;
                case "meta" -> meta = ModifierValue.DOWN;
                case "alt" -> alt = ModifierValue.DOWN;
                case "altGraph", "altGraphKey" -> {
                    // not representable
                }
                case "pressed", "released" -> {
                    // the next token carries the key
                }
                case "typed" -> {
                    shift = ModifierValue.UP;
                    ctrl = ModifierValue.UP;
                    meta = ModifierValue.UP;
                    alt = ModifierValue.UP;
                }
                default -> {
                    if (token.startsWith("button")) {
                        // mouse chords are ignored
                    } else if (key == null) {
                        key = token;
                    } else {
                        LOGGER.warn("Unrecognized keystroke spec '{}' (extra token {})", spec,
                            token);
                        return Optional.empty();
                    }
                }
            }
        }
        if (key == null) {
            return Optional.empty();
        }
        KeyCode code;
        try {
            code = KeyCode.valueOf(key);
        } catch (IllegalArgumentException e) {
            LOGGER.warn("Unknown key name '{}' in the keystroke spec '{}'", key, spec);
            return Optional.empty();
        }
        if (isModifier(code)) {
            return Optional.empty();
        }
        return Optional.of(new KeyCodeCombination(code, shift, ctrl, alt, meta,
            ModifierValue.ANY));
    }

    /**
     * Formats a {@link KeyCombination} as a Swing {@code KeyStroke.toString()} spec, e.g.
     * {@code "shift ctrl pressed P"}. The {@code SHORTCUT} modifier resolves to {@code ctrl} on
     * non-Mac platforms and {@code meta} on Mac. Key names are the JavaFX {@link KeyCode} names,
     * which are the Swing {@code VK_*} constant names for all default shortcuts (the human
     * readable {@link KeyCode#getName()} would emit e.g. {@code "Space"}, which neither Swing nor
     * this parser accept); exotic codes may produce names the Swing parser rejects (logged as a
     * warning on the next load).
     *
     * @param combination the combination
     * @return the Swing spec
     */
    public static String toSwingSpec(KeyCombination combination) {
        if (!(combination instanceof KeyCodeCombination codeCombination)) {
            LOGGER.warn("Cannot convert {} into the Swing keystroke format", combination);
            return combination.getName();
        }
        StringBuilder builder = new StringBuilder();
        if (codeCombination.getShift() == ModifierValue.DOWN) {
            builder.append("shift ");
        }
        if (codeCombination.getControl() == ModifierValue.DOWN
                || (codeCombination.getShortcut() == ModifierValue.DOWN && !MAC)) {
            builder.append("ctrl ");
        }
        if (codeCombination.getMeta() == ModifierValue.DOWN
                || (codeCombination.getShortcut() == ModifierValue.DOWN && MAC)) {
            builder.append("meta ");
        }
        if (codeCombination.getAlt() == ModifierValue.DOWN) {
            builder.append("alt ");
        }
        builder.append("pressed ").append(codeCombination.getCode().name());
        return builder.toString();
    }

    /**
     * @param code a key code
     * @return whether the code is a modifier key (those do not form complete shortcuts)
     */
    public static boolean isModifier(KeyCode code) {
        return switch (code) {
            case CONTROL, SHIFT, ALT, META, ALT_GRAPH, SHORTCUT, COMMAND, WINDOWS, CONTEXT_MENU,
                    CAPS, NUM_LOCK, SCROLL_LOCK ->
                true;
            default -> false;
        };
    }
}
