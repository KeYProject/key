/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli;

import java.nio.file.Path;

import org.jspecify.annotations.Nullable;

/**
 * Renders a {@link ContractResult} as a single line of the machine-readable {@code KEY_RESULT}
 * protocol (§2 of the headless interface contract). The output is hand-rolled so that it is
 * byte-exact: no whitespace beyond the mandated single space after the prefix, JSON escaping only
 * for the string fields, and literal {@code null} for absent optional values.
 */
public final class ResultRecordWriter {

    /// The literal protocol prefix of every result line.
    public static final String PREFIX = "KEY_RESULT ";

    /**
     * Renders the given result as a single {@code KEY_RESULT} line without trailing newline.
     *
     * @param result the result to render
     * @return the byte-exact protocol line
     */
    public String toJsonLine(ContractResult result) {
        StringBuilder sb = new StringBuilder(PREFIX.length() + 128);
        sb.append(PREFIX).append('{');
        sb.append("\"version\":1");
        sb.append(",\"contract\":\"").append(escape(result.contract())).append('"');
        sb.append(",\"status\":\"").append(result.status().statusString()).append('"');
        sb.append(",\"openGoals\":").append(result.openGoals());
        sb.append(",\"elapsedMs\":").append(result.elapsedMs());
        sb.append(",\"proofFile\":").append(renderPath(result.proofFile()));
        sb.append(",\"smtCalls\":").append(result.smtCalls());
        sb.append(",\"smtProved\":").append(result.smtProved());
        sb.append(",\"errorMessage\":").append(renderString(result.errorMessage()));
        sb.append('}');
        return sb.toString();
    }

    private static String renderPath(@Nullable Path proofFile) {
        return proofFile == null ? "null" : renderString(proofFile.toString());
    }

    private static String renderString(@Nullable String value) {
        return value == null ? "null" : "\"" + escape(value) + "\"";
    }

    /**
     * Escapes a string for inclusion in the JSON object: quotes, backslashes and control
     * characters become their JSON escape sequences.
     *
     * @param value the raw string
     * @return the JSON-safe string (without surrounding quotes)
     */
    static String escape(String value) {
        StringBuilder sb = new StringBuilder(value.length() + 16);
        for (int i = 0; i < value.length(); i++) {
            char c = value.charAt(i);
            switch (c) {
                case '"' -> sb.append("\\\"");
                case '\\' -> sb.append("\\\\");
                case '\n' -> sb.append("\\n");
                case '\r' -> sb.append("\\r");
                case '\t' -> sb.append("\\t");
                case '\b' -> sb.append("\\b");
                case '\f' -> sb.append("\\f");
                default -> {
                    if (c < 0x20) {
                        sb.append(String.format("\\u%04x", (int) c));
                    } else {
                        sb.append(c);
                    }
                }
            }
        }
        return sb.toString();
    }
}
