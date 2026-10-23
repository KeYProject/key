/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.Choice;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.Nullable;

/**
 * The taclet-management support of the KeY-Agent: listing the taclets and taclet options of a
 * proof, exporting taclets as parseable KeY rule declarations, and registering/removing taclets
 * at runtime.
 *
 * <p>
 * All methods are proof-scoped: taclets live in the proof's {@link InitConfig} (the
 * choice-filtered set exposed by {@link InitConfig#activatedTaclets()}) and in the per-goal
 * {@code TacletIndex}. Adding or removing a taclet therefore reconciles both the proof-wide rule
 * list and the indices of the currently open goals, following the same pattern as the GUI's
 * lemma generation ({@code LemmaGenerationAction}) and {@code TacletLoader}.
 *
 * <p>
 * Methods never throw for expected failures; they return a human-readable text starting with
 * {@code "Error: "} instead, as expected by the agent tool layer.
 *
 * @author Alexander Weigl
 */
public final class TacletOperations {

    private TacletOperations() {
    }

    /** The names of the taclets available for the proof, sorted, optionally filtered. */
    public static String listTaclets(Proof proof, @Nullable String filter) {
        var names = nameList(proof, filter);
        if (names.isEmpty()) {
            return filter == null || filter.isBlank() ? "(no taclets are available)"
                    : "(no taclets matching \"" + filter + "\")";
        }
        var sb = new StringBuilder();
        sb.append(names.size()).append(" taclet(s):\n");
        for (var name : names) {
            sb.append("- ").append(name).append('\n');
        }
        return sb.toString().stripTrailing();
    }

    /** The current taclet options (choices) of the proof, one line per category. */
    public static String listTacletOptions(Proof proof) {
        var initConfig = proof.getInitConfig();
        var settings = proof.getSettings().getChoiceSettings();
        var possible = new LinkedHashMap<String, List<String>>();
        settings.getCategory2Choices().forEach(
            (cat, values) -> possible.put(cat, values.stream().sorted().toList()));
        // effective selection: the activated choices may differ from the settings mirror
        var selected = new LinkedHashMap<String, String>();
        initConfig.getActivatedChoices().forEach(c -> selected.put(c.category(), optionOf(c)));
        settings.getDefaultChoices().forEach((cat, value) -> selected.putIfAbsent(cat, value));
        for (var cat : selected.keySet()) {
            possible.computeIfAbsent(cat, c -> List.of());
        }
        if (possible.isEmpty()) {
            return "(no taclet options configured)";
        }
        var sb = new StringBuilder();
        possible.entrySet().stream().sorted(Map.Entry.comparingByKey()).forEach(e -> {
            var cat = e.getKey();
            var current = selected.getOrDefault(cat, "?");
            sb.append(cat).append(": ").append(current);
            var values = e.getValue();
            if (!values.isEmpty()) {
                sb.append(" (possible: ").append(String.join(", ", values)).append(')');
            }
            sb.append('\n');
        });
        return sb.toString().stripTrailing();
    }

    /** Exports the named taclet as a parseable KeY rule declaration. */
    public static String exportTaclet(Proof proof, String tacletName) {
        var taclet = findTaclet(proof, tacletName);
        if (taclet == null) {
            return "Error: no taclet named \"" + tacletName + "\"";
        }
        var printed = printTaclet(proof, taclet);
        return printed == null
                ? "Error: could not export taclet \"" + tacletName + "\""
                : printed;
    }

    /**
     * Exports all taclets of the proof (optionally filtered by name substring) as parseable KeY
     * rule declarations, bounded by the proof-context character budget.
     */
    public static String exportTaclets(Proof proof, @Nullable String filter) {
        var names = nameList(proof, filter);
        if (names.isEmpty()) {
            return filter == null || filter.isBlank() ? "(no taclets are available)"
                    : "(no taclets matching \"" + filter + "\")";
        }
        int cap = Math.max(2000, LlmSettings.INSTANCE.getProofContextMaxChars());
        var sb = new StringBuilder();
        sb.append(names.size()).append(" taclet(s):\n");
        List<String> omitted = new ArrayList<>();
        for (var name : names) {
            var printed = printTaclet(proof, findTaclet(proof, name));
            if (printed == null) {
                omitted.add(name);
                continue;
            }
            var block = "\n\n" + printed;
            if (sb.length() + block.length() > cap && sb.length() > 0) {
                omitted.add(name);
                continue;
            }
            sb.append(block);
        }
        sb.append('\n');
        if (!omitted.isEmpty()) {
            sb.append("[omitted: ").append(omitted.size()).append(" taclet(s)");
            if (omitted.size() <= 10) {
                sb.append(" (").append(String.join(", ", omitted)).append(')');
            }
            sb.append(" — use a 'filter' to narrow the output or export single taclets"
                + " with export_taclet]");
        }
        return sb.toString().stripTrailing();
    }

    /**
     * Parses a KeY rule declaration and registers the resulting taclet(s) for the given proof:
     * the proof-wide rule list is extended and the taclet is made applicable at all open goals.
     * Past rule applications are not affected.
     */
    public static String addTaclet(Proof proof, String tacletSource) {
        var source = normalize(tacletSource);
        if (source == null || source.isBlank()) {
            return "Error: empty taclet declaration";
        }
        InitConfig config = proof.getInitConfig();
        List<Taclet> parsed;
        try {
            parsed = parseSource(config.copy(), source);
        } catch (Exception e) {
            return "Error: could not parse taclet declaration: " + e.getMessage();
        }
        if (parsed.isEmpty()) {
            return "Error: the declaration contains no taclet";
        }
        var names = new ArrayList<String>();
        for (var taclet : parsed) {
            var name = taclet.name().toString();
            if (findTaclet(proof, name) != null) {
                return "Error: taclet \"" + name + "\" already exists; remove it first";
            }
            names.add(name);
        }
        config.setTaclets(config.getTaclets().prependReverse(parsed));
        int openGoals = proof.openGoals().size();
        for (var taclet : parsed) {
            for (Goal goal : proof.openGoals()) {
                goal.addTaclet(taclet, SVInstantiations.EMPTY_SVINSTANTIATIONS, false);
            }
        }
        names.sort(String::compareTo);
        return names.size() == 1
                ? "Registered taclet \"" + names.get(0) + "\" at " + openGoals
                    + " open goal(s); it is now available for future rule applications."
                : "Registered taclet(s) " + String.join(", ", names) + " at " + openGoals
                    + " open goal(s); they are now available for future rule applications.";
    }

    /**
     * Removes the named taclet from the proof: the proof-wide rule list is rebuilt without it and
     * the taclet is removed from the indices of all open goals. Past rule applications are not
     * rewritten.
     */
    public static String removeTaclet(Proof proof, String tacletName) {
        var taclet = findTaclet(proof, tacletName);
        if (taclet == null) {
            return "Error: no taclet named \"" + tacletName + "\"";
        }
        InitConfig config = proof.getInitConfig();
        var remaining = config.getTaclets().stream()
                .filter(t -> !t.name().equals(taclet.name())).toList();
        config.setTaclets(ImmutableList.fromList(remaining));
        config.getTaclet2Builder().remove(taclet);
        int openGoals = 0;
        for (Goal goal : proof.openGoals()) {
            var index = goal.ruleAppIndex();
            var apps = index.tacletIndex().allNoPosTacletApps().stream()
                    .filter(app -> app.taclet() == taclet).toList();
            for (var app : apps) {
                index.removeNoPosTacletApp(app);
            }
            openGoals++;
        }
        return "Removed taclet \"" + tacletName + "\" from " + openGoals
            + " open goal(s); future rule applications will not offer it.";
    }

    // ----------------------------------------------------------------------- internals

    private static List<String> nameList(Proof proof, @Nullable String filter) {
        var needle = filter == null ? null : filter.toLowerCase(Locale.ROOT);
        return proof.getInitConfig().activatedTaclets().stream()
                .map(t -> t.name().toString())
                .filter(name -> needle == null || needle.isBlank()
                        || name.toLowerCase(Locale.ROOT).contains(needle))
                .sorted(Comparator.comparing(String::toLowerCase, Comparator.naturalOrder()))
                .toList();
    }

    private static @Nullable Taclet findTaclet(Proof proof, String tacletName) {
        return proof.getInitConfig().getTaclets().stream()
                .filter(t -> t.name().toString().equals(tacletName)).findFirst().orElse(null);
    }

    /** Prints a taclet with its schema variables declared, without pretty syntax. */
    private static @Nullable String printTaclet(Proof proof, @Nullable Taclet taclet) {
        if (taclet == null) {
            return null;
        }
        try {
            Services services = proof.getServices();
            var notation = new NotationInfo();
            notation.refresh(services, false, false, false);
            var printer = LogicPrinter.purePrinter(notation, services);
            printer.printTaclet(taclet);
            var text = printer.result().strip();
            // The printer renders formula schema variables as "\formula Formula b;" but the rule
            // grammar accepts "\formula b;" (formula variable sorts are implicit). Drop the
            // redundant sort name so the export round-trips through the parser.
            text = text.replace("\\schemaVar \\formula Formula ", "\\schemaVar \\formula ");
            return text;
        } catch (RuntimeException e) {
            return null;
        }
    }

    private static List<Taclet> parseSource(InitConfig context, String source)
            throws java.io.IOException {
        var io = new KeyIO(context.getServices(), context.namespaces());
        return io.load(source).loadComplete();
    }

    /**
     * Accepts a bare {@code name { ... }} declaration, an optional legacy {@code \taclet}
     * keyword prefix, or a complete {@code \rules { ... }} block.
     */
    private static @Nullable String normalize(String source) {
        if (source == null) {
            return null;
        }
        var s = source.strip();
        if (s.startsWith("\\taclet")) {
            s = s.substring("\\taclet".length()).strip();
        }
        if (s.endsWith(";")) {
            s = s.substring(0, s.length() - 1).stripTrailing();
        }
        if (!s.contains("\\rules")) {
            s = "\n\\rules { " + s + "; }";
        }
        return s;
    }

    /** The selected value of a choice, i.e. the part after the category separator. */
    private static String optionOf(Choice choice) {
        var full = choice.name().toString();
        int idx = full.indexOf(':');
        return idx >= 0 ? full.substring(idx + 1) : full;
    }
}
