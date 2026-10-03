/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.key.llm;

import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;
import java.util.regex.Pattern;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import org.jspecify.annotations.Nullable;

/**
 * Resolves the light-weight markup used in the input box:
 * <ul>
 * <li>{@code $name} - context tokens ({@code $seq}, {@code $goals}, {@code $proof},
 * {@code $proofName}, {@code $computePath}, {@code $model}, {@code $classpath},
 * {@code $bootClasspath}, {@code $selectedFiles})</li>
 * <li>{@code @path/to/file.java} - reference to a file inside the model directory</li>
 * <li>{@code /skill:name} - activate a skill for this turn (directive is stripped)</li>
 * <li>{@code /skills}, {@code /prompts} - inline listings</li>
 * </ul>
 *
 * @author Alexander Weigl
 */
public final class PromptResolver {
    private static final Pattern TOKEN =
        Pattern.compile("\\$([a-zA-Z][a-zA-Z0-9]*)");
    private static final Pattern FILE_REF = Pattern.compile("@([\\w.\\-/\\\\]+\\.[a-zA-Z0-9]+)");
    private static final Pattern SKILL_DIRECTIVE = Pattern.compile("/skill:([a-zA-Z0-9_-]+)");
    private static final Pattern PROMPT_DIRECTIVE = Pattern.compile("/prompt:([a-zA-Z0-9_-]+)");

    private PromptResolver() {
    }

    /** The outcome of resolving one user message. */
    public record Result(String text, @Nullable String skillName, List<String> warnings) {
    }

    /** Read-only access to the pieces needed for resolving (testable without a UI). */
    public interface Context {
        @Nullable
        Proof proof();

        @Nullable
        Node node();
    }

    /**
     * Resolves the markup in {@code raw} using the given session (for files/selectedFiles) and
     * current proof state.
     */
    public static Result resolve(String raw, LlmSession session, Context ctx) {
        var warnings = new ArrayList<String>();
        String text = raw;

        // /skills and /prompts listings
        if (text.contains("/skills")) {
            text = text.replace("/skills", listOf(SkillLibrary.INSTANCE.all(), Skill::name,
                Skill::description));
        }
        if (text.contains("/prompts")) {
            text = text.replace("/prompts",
                listOf(PromptLibrary.INSTANCE.all(), Prompt::name, Prompt::description));
        }

        // /skill:name directive
        String skillName = null;
        var m = SKILL_DIRECTIVE.matcher(text);
        if (m.find()) {
            var name = m.group(1);
            var skill = SkillLibrary.INSTANCE.get(name);
            if (skill != null && skill.enabled()) {
                skillName = name;
                text = text.replace(m.group(), "");
            } else {
                warnings.add("Unknown or disabled skill: " + name);
            }
        }

        // /prompt:name directives "extend the prompt": the rendered template replaces the directive
        // and is resolved together with the remaining $tokens/@files references.
        var promptMatcher = PROMPT_DIRECTIVE.matcher(text);
        var promptResolved = new StringBuilder();
        int promptLast = 0;
        while (promptMatcher.find()) {
            var name = promptMatcher.group(1);
            var prompt = PromptLibrary.INSTANCE.get(name);
            if (prompt != null) {
                promptResolved.append(text, promptLast, promptMatcher.start())
                        .append(prompt.template());
            } else {
                warnings.add("Unknown prompt: " + name);
                promptResolved.append(text, promptLast, promptMatcher.end())
                        .append("[unknown prompt: ").append(name).append("]");
            }
            promptLast = promptMatcher.end();
        }
        promptResolved.append(text.substring(promptLast));
        text = promptResolved.toString();

        // $tokens
        var tokenMatcher = TOKEN.matcher(text);
        var resolved = new StringBuilder();
        int last = 0;
        while (tokenMatcher.find()) {
            var repl = token(tokenMatcher.group(1), session, ctx);
            if (repl == null) {
                repl = "[unknown token $" + tokenMatcher.group(1) + "]";
            }
            resolved.append(text, last, tokenMatcher.start()).append(repl);
            last = tokenMatcher.end();
        }
        resolved.append(text.substring(last));
        text = resolved.toString();

        // @file references
        var fileMatcher = FILE_REF.matcher(text);
        var fileResolved = new StringBuilder();
        last = 0;
        while (fileMatcher.find()) {
            var pathName = fileMatcher.group(1);
            var repl = fileContent(pathName, session, ctx, warnings);
            fileResolved.append(text, last, fileMatcher.start()).append(repl);
            last = fileMatcher.end();
        }
        fileResolved.append(text.substring(last));
        text = fileResolved.toString();

        return new Result(text.trim(), skillName, warnings);
    }

    private static <T> String listOf(List<T> items, Function<T, String> nameFn,
            Function<T, String> descFn) {
        var sb = new StringBuilder();
        if (items.isEmpty()) {
            return "(none defined)";
        }
        for (var item : items) {
            sb.append("  - ").append(nameFn.apply(item)).append(": ").append(descFn.apply(item))
                    .append('\n');
        }
        return sb.toString();
    }

    /** Resolves a single {@code $token}. */
    public static @Nullable String token(String token, LlmSession session, Context ctx) {
        var proof = ctx.proof();
        var node = ctx.node();
        return switch (token) {
            case "seq" -> proof != null ? ProofContextCollector.sequentText(node, proof) : null;
            case "goals" -> proof != null
                    ? ProofContextCollector.openGoalsSummary(proof,
                        LlmSettings.INSTANCE.getProofContextMaxSequents())
                    : null;
            case "proof" -> proof != null ? ProofContextCollector.proofStatus(proof) : null;
            case "proofName" -> proof != null ? ProofContextCollector.proofName(proof) : null;
            case "computePath" ->
                ProofContextCollector.computePath(node,
                    Math.max(1, LlmSettings.INSTANCE.getMaxToolRounds() * 12));
            case "model" -> proof != null ? ProofContextCollector.modelInfo(proof) : null;
            case "classpath" -> proof != null ? classPathOf(proof) : null;
            case "bootClasspath" -> proof != null ? bootClassPathOf(proof) : null;
            case "selectedFiles" -> selectedFilesOf(session);
            default -> null;
        };
    }

    private static @Nullable String classPathOf(Proof proof) {
        var jm = proof.getEnv().getServicesForEnvironment().getJavaModel();
        if (jm == null || jm.getClassPath() == null) {
            return "(none)";
        }
        return String.valueOf(jm.getClassPath());
    }

    private static @Nullable String bootClassPathOf(Proof proof) {
        var jm = proof.getEnv().getServicesForEnvironment().getJavaModel();
        if (jm == null) {
            return "(none)";
        }
        return jm.getBootClassPath() == null ? "(none)" : jm.getBootClassPath().toString();
    }

    private static String selectedFilesOf(LlmSession session) {
        if (session.getSelectedFiles().isEmpty()) {
            return "(no files selected)";
        }
        var sb = new StringBuilder();
        for (var uri : session.getSelectedFiles()) {
            sb.append("  - ").append(uri).append('\n');
        }
        return sb.toString().strip();
    }

    /** Reads an {@code @file} reference (relative to the model dir) into a code block. */
    private static String fileContent(String pathName, LlmSession session, Context ctx,
            List<String> warnings) {
        var proof = ctx.proof();
        if (proof == null) {
            return "[file: " + pathName + " (no proof loaded)]";
        }
        Path resolved = FileAccess.resolveInModel(proof, pathName);
        if (resolved == null) {
            // maybe the reference is an absolute file URI?
            try {
                resolved = Path.of(pathName);
            } catch (IllegalArgumentException e) {
                resolved = null;
            }
            if (resolved == null) {
                return "[file not found: " + pathName + "]";
            }
        }
        if (FileAccess.isBinary(pathName)) {
            return "[binary file, not embedded: " + pathName + "]";
        }
        try {
            var content = FileAccess.readText(resolved);
            return "```\n" + pathName + "\n" + content + "\n```";
        } catch (IOException e) {
            warnings.add("could not read file " + pathName + ": " + e.getMessage());
            return "[file not found: " + pathName + "]";
        }
    }
}
