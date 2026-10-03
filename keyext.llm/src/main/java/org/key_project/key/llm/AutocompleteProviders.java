/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.key.llm;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.gui.MainWindow;

/**
 * Built-in completion providers for the chat input:
 * <ul>
 * <li>{@code $} - context tokens</li>
 * <li>{@code @} - files of the current Java model</li>
 * <li>{@code /} - skills, prompts and library management entries</li>
 * </ul>
 *
 * @author Alexander Weigl
 */
public final class AutocompleteProviders {
    private static final Map<String, String> TOKEN_DESCRIPTIONS = new LinkedHashMap<>();

    static {
        TOKEN_DESCRIPTIONS.put("seq", "the current sequent");
        TOKEN_DESCRIPTIONS.put("goals", "the open goals");
        TOKEN_DESCRIPTIONS.put("proof", "proof status (open/closed goals, node count)");
        TOKEN_DESCRIPTIONS.put("proofName", "name of the current proof");
        TOKEN_DESCRIPTIONS.put("computePath", "applied rules from the root to the selected node");
        TOKEN_DESCRIPTIONS.put("model", "Java model directory and class paths");
        TOKEN_DESCRIPTIONS.put("classpath", "Java class path");
        TOKEN_DESCRIPTIONS.put("bootClasspath", "Java boot class path");
        TOKEN_DESCRIPTIONS.put("selectedFiles", "the files attached in this chat");
    }

    private AutocompleteProviders() {
    }

    /** Completions for {@code $}: context tokens. */
    public static AutocompleteInput.CompletionProvider contextTokens() {
        return new AutocompleteInput.CompletionProvider() {
            @Override
            public char trigger() {
                return '$';
            }

            @Override
            public List<AutocompleteInput.Suggestion> apply(String prefix) {
                var result = new ArrayList<AutocompleteInput.Suggestion>();
                for (var e : TOKEN_DESCRIPTIONS.entrySet()) {
                    if (e.getKey().startsWith(prefix)) {
                        result.add(new AutocompleteInput.Suggestion("$" + e.getKey() + " ",
                            "$" + e.getKey(), e.getValue()));
                    }
                }
                return result;
            }
        };
    }

    /** Completions for {@code @}: files of the current Java model. */
    public static AutocompleteInput.CompletionProvider files() {
        return new AutocompleteInput.CompletionProvider() {
            @Override
            public char trigger() {
                return '@';
            }

            @Override
            public List<AutocompleteInput.Suggestion> apply(String prefix) {
                var mediator = MainWindow.getInstance().getMediator();
                var proof = mediator == null ? null : mediator.getSelectedProof();
                var result = new ArrayList<AutocompleteInput.Suggestion>();
                for (var path : FileAccess.listFiles(proof)) {
                    var rel = FileAccess.relativeName(proof, path);
                    if (rel == null) {
                        continue;
                    }
                    if (prefix.isEmpty() || rel.startsWith(prefix)) {
                        result.add(new AutocompleteInput.Suggestion("@" + rel + " ", "@" + rel,
                            path.getFileName().toString()));
                    }
                }
                return result;
            }
        };
    }

    /**
     * Completions for {@code /}: skills, prompts and entries that open the library dialogs.
     *
     * @param openPromptDialog callback to create a new prompt
     * @param openSkillDialog callback to create a new skill
     */
    public static AutocompleteInput.CompletionProvider commands(Runnable openPromptDialog,
            Runnable openSkillDialog) {
        return new AutocompleteInput.CompletionProvider() {
            @Override
            public char trigger() {
                return '/';
            }

            @Override
            public List<AutocompleteInput.Suggestion> apply(String prefix) {
                var result = new ArrayList<AutocompleteInput.Suggestion>();
                addCommands(result, prefix, "/skills", "list all skills", null);
                addCommands(result, prefix, "/prompts", "list all prompts", null);
                for (var skill : SkillLibrary.INSTANCE.all()) {
                    if (skill.enabled()) {
                        addCommands(result, prefix, "/skill:" + skill.name(),
                            "skill \u2014 " + skill.description(), null);
                    }
                }
                for (var prompt : PromptLibrary.INSTANCE.all()) {
                    addCommands(result, prefix, "/prompt:" + prompt.name(),
                        "prompt \u2014 " + prompt.description(), null);
                }
                addCommands(result, prefix, "\uD83D\uDDD2 new prompt\u2026", "create a new prompt",
                    openPromptDialog);
                addCommands(result, prefix, "\uD83D\uDDD2 new skill\u2026", "create a new skill",
                    openSkillDialog);
                return result;
            }

            private void addCommands(List<AutocompleteInput.Suggestion> result, String prefix,
                    String text, String detail, Runnable action) {
                if (prefix.isEmpty() || text.startsWith(prefix)) {
                    result.add(
                        new AutocompleteInput.Suggestion(text + (action == null ? " " : null),
                            text, detail, action));
                }
            }
        };
    }
}
