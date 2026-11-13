/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

/**
 * Derives the concrete OpenAI-compatible endpoint URLs (chat completions, model listing) from the
 * API base URL configured by the user. Different gateway deployments expose those operations under
 * different path conventions, and the configured base may or may not already contain the
 * convention's prefix:
 *
 * <ul>
 * <li><b>Open WebUI</b> (e.g. {@code https://ki-toolbox.scc.kit.edu}): operations live under
 * {@code /openai/…} (also served by LiteLLM's {@code /openai} catch-all) — a <em>bare</em>
 * base URL (host only) gets {@code /openai/chat/completions} and {@code /openai/models}
 * appended.</li>
 * <li><b>OpenAI / LiteLLM convention</b> (e.g. {@code https://litellm.scc.kit.edu/v1}): if the
 * base URL already ends in a versioned API root ({@code /v1}, {@code /api/v1}) or points
 * into an API root ({@code /openai}, {@code /api}), only the operation name is appended —
 * {@code …/v1/chat/completions}, {@code …/api/models}.</li>
 * <li>If the base already ends with the full operation path ({@code /chat/completions} or
 * {@code /models}), it is used as given (and the sibling operation is derived from it).</li>
 * </ul>
 *
 * @author Alexander Weigl
 */
public final class ApiUrls {

    /** The OpenAI-compatible path of the chat-completions operation, relative to an API root. */
    public static final String COMPLETIONS_PATH = "/chat/completions";

    /** The OpenAI-compatible path of the model-listing operation, relative to an API root. */
    public static final String MODELS_PATH = "/models";

    /**
     * The gateway-dependent prefix put in front of the operation paths when the base URL does not
     * already contain one: Open WebUI serves {@code /openai/…} on the bare host, and LiteLLM
     * accepts it through its {@code /openai/{endpoint}} catch-all.
     */
    public static final String DEFAULT_PREFIX = "/openai";

    private ApiUrls() {
    }

    /** Strips whitespace and trailing slashes from a configured base URL. */
    public static String normalize(String baseUrl) {
        var base = baseUrl == null ? "" : baseUrl.strip();
        while (base.endsWith("/")) {
            base = base.substring(0, base.length() - 1);
        }
        return base;
    }

    /** The chat-completions URL for the given configured base URL. */
    public static String chatCompletions(String baseUrl) {
        return derive(baseUrl, COMPLETIONS_PATH, MODELS_PATH);
    }

    /** The model-listing URL for the given configured base URL. */
    public static String models(String baseUrl) {
        return derive(baseUrl, MODELS_PATH, COMPLETIONS_PATH);
    }

    /**
     * Derivation: if the base already ends with the wanted operation path, use it as is; if it
     * ends with the sibling operation path, replace the sibling; if it ends in a known API root
     * (a versioned or service prefix), append only the operation path; otherwise append the
     * gateway-dependent prefix and the operation path.
     */
    private static String derive(String baseUrl, String path, String siblingPath) {
        var base = normalize(baseUrl);
        if (base.endsWith(path)) {
            return base;
        }
        if (base.endsWith(siblingPath)) {
            return base.substring(0, base.length() - siblingPath.length()) + path;
        }
        var prefix = atApiRoot(base) ? "" : DEFAULT_PREFIX;
        return base + prefix + path;
    }

    /**
     * True if the base URL already ends in a recognized API root ({@code /v1}, {@code /api/v1}, …).
     */
    private static boolean atApiRoot(String base) {
        var lower = base.toLowerCase(java.util.Locale.ROOT);
        return lower.endsWith("/v1") || lower.endsWith("/openai") || lower.endsWith("/api")
                || lower.endsWith("/openai/v1") || lower.endsWith("/api/v1");
    }
}
