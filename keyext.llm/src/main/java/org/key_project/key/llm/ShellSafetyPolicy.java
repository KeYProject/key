/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Pattern;

/**
 * Blocks dangerous shell commands before they reach the OS. The policy is defense-in-depth:
 * approval of the {@code run_command} tool asks the user for consent, but a command matching one
 * of the blocklist patterns is refused regardless of approval.
 * <p>
 * The built-in patterns cover destructive/privilege-escalating commands; users can extend the list
 * through {@code LlmSettings.shellBlockedPatterns}.
 *
 * @author Alexander Weigl
 */
public final class ShellSafetyPolicy {

    /** The outcome of checking a command. */
    public record Verdict(boolean allowed, String reason) {

        public static Verdict ok() {
            return new Verdict(true, "");
        }

        public static Verdict blocked(String reason) {
            return new Verdict(false, reason);
        }
    }

    private final List<Pattern> blockedPatterns;

    public ShellSafetyPolicy(List<String> patterns) {
        var compiled = new ArrayList<Pattern>(patterns.size());
        for (String p : patterns) {
            if (p == null || p.isBlank()) {
                continue;
            }
            try {
                compiled.add(Pattern.compile(p));
            } catch (Exception e) {
                // ignore invalid user-defined patterns
            }
        }
        this.blockedPatterns = List.copyOf(compiled);
    }

    public ShellSafetyPolicy() {
        this(LlmSettings.INSTANCE.getEffectiveShellBlockedPatterns());
    }

    /**
     * Evaluates the command against the blocklist (case-insensitive).
     *
     * @param command the raw command line
     * @return {@link Verdict#allowed() allowed} or a blocked verdict with the matching pattern
     */
    public Verdict evaluate(String command) {
        if (command == null || command.isBlank()) {
            return Verdict.blocked("empty command");
        }
        for (Pattern pattern : blockedPatterns) {
            if (pattern.matcher(command).find()) {
                return Verdict.blocked("command matches blocked pattern: " + pattern.pattern());
            }
        }
        return Verdict.ok();
    }
}
