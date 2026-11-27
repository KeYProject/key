/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

import com.google.gson.GsonBuilder;

/**
 * The {@code tools} facade bound to the {@code execute} snippets: the sanctioned Java API for a
 * script to reach the agent's tools. Each method dispatches the corresponding tool call through
 * the {@link ToolDispatcher} (synchronous, serialized with all other tool calls) and returns its
 * stringified result - exactly what the model would receive. Because the script itself was
 * approved as one unit, the facade's calls do not ask for approval again.
 * <p>
 * Interactive tools ({@code question}, {@code skill}, {@code subagent}, {@code execute}) are not
 * exposed as methods: they pause the agent loop and cannot run from inside a snippet; the
 * generic {@link #call(String, String)} reaches every registered tool and returns the tools'
 * own explanatory placeholders for them.
 * <p>
 * The facade of a running script is published under a fresh per-execution key
 * ({@link #register(String, ToolFacade)}); the {@code execute} preamble binds it to the
 * snippet's {@code tools} variable via {@link #byKey(String)} and unregisters it afterwards.
 *
 * @author Alexander Weigl
 */
public final class ToolFacade {

    /** The facades of the running snippets, keyed by their per-execution key. */
    private static final Map<String, ToolFacade> REGISTRY = new ConcurrentHashMap<>();

    private final LlmSession session;

    /** Creates the facade for one session (bound by the {@code execute} preamble). */
    public ToolFacade(LlmSession session) {
        this.session = session;
    }

    /** Publishes {@code facade} under {@code key} for the duration of one snippet execution. */
    public static void register(String key, ToolFacade facade) {
        REGISTRY.put(key, facade);
    }

    /** Removes the registration of {@code key} (the snippet execution has ended). */
    public static void unregister(String key) {
        REGISTRY.remove(key);
    }

    /** The facade of the running snippet with the given key, or {@code null} if unknown. */
    public static ToolFacade byKey(String key) {
        return REGISTRY.get(key);
    }

    // --------------------------------------------------------------------- file tools

    /** {@code glob}: matches the files of the model against a glob pattern. */
    public String glob(String pattern) {
        return call("glob", Map.of("pattern", pattern));
    }

    /** {@code read}: reads a model file from its first line. */
    public String read(String path) {
        return read(path, 1, 2000);
    }

    /** {@code read}: reads a model file from {@code offset} on. */
    public String read(String path, int offset) {
        return read(path, offset, 2000);
    }

    /** {@code read}: reads at most {@code limit} lines of a model file from {@code offset} on. */
    public String read(String path, int offset, int limit) {
        return call("read", Map.of("path", path, "offset", offset, "limit", limit));
    }

    /** {@code grep}: searches the model tree for a pattern (regular expression). */
    public String grep(String pattern) {
        return call("grep", Map.of("pattern", pattern));
    }

    /** {@code grep}: searches the model tree for a pattern, restricted by an include glob. */
    public String grep(String pattern, String include) {
        return call("grep", Map.of("pattern", pattern, "include", include));
    }

    /** {@code write}: creates or overwrites a model file. */
    public String write(String path, String content) {
        return call("write", Map.of("path", path, "content", content));
    }

    /** {@code edit}: performs an exact string replacement in a model file. */
    public String edit(String path, String oldString, String newString) {
        return call("edit", Map.of("path", path, "oldString", oldString, "newString", newString));
    }

    /** {@code shell}: runs a shell command in the model directory (blocklist applies). */
    public String shell(String command) {
        return call("shell", Map.of("command", command));
    }

    // --------------------------------------------------------------------- web tools

    /** {@code webfetch}: fetches a web page as Markdown. */
    public String webfetch(String url) {
        return call("webfetch", Map.of("url", url));
    }

    /** {@code websearch}: searches the web with the configured endpoint. */
    public String websearch(String query) {
        return call("websearch", Map.of("query", query));
    }

    // --------------------------------------------------------------------- generic

    /**
     * Dispatches any registered tool by name (proof tools included). Intercepted tools
     * ({@code question}, {@code skill}, {@code subagent}, {@code execute}) return their
     * explanatory placeholders.
     */
    public String call(String name, String argumentsJson) {
        try {
            return session.getToolDispatcher().callNow(session, name, argumentsJson);
        } catch (Exception e) {
            return "Error: tool " + name + " failed: " + e.getMessage();
        }
    }

    /** {@code list_tools}: the Markdown documentation of all registered tools. */
    public String listTools() {
        return call("list_tools", "{}");
    }

    /** Dispatches a tool call with the given named arguments (JSON-encoded by this method). */
    public String call(String name, Map<String, Object> arguments) {
        var json = new GsonBuilder().create().toJson(arguments);
        return call(name, json == null ? "{}" : json);
    }
}
