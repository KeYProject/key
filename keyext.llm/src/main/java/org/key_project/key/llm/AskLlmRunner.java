/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import org.key_project.key.llm.mcp.AgentTool;

/**
 * Executes one {@code ask_llm} call: a fresh one-shot chat completion against the session's
 * chat-completion endpoint with a CLEAN context - no conversation history, no tools, only the
 * caller's {@code prompt} (plus an optional {@code system} prompt). The reply text is delivered
 * back to the caller, so the delegating agent can think about itself: review its own plan,
 * play devil's advocate, summarize a pile of tool output, or ask a different model (the optional
 * {@code model} override) for a second opinion.
 * <p>
 * Like {@code spawn_subagent}, the call is intercepted by the agent loop (and the sub-agent child
 * loops) and runs via {@link ToolDispatcher#submitTask} - deliberately <em>without</em> the
 * dispatch lock: an HTTP round-trip of several seconds must not stall parallel sub-agents or other
 * sessions' tool calls. It never dispatches tools itself, so no nested locking is possible.
 *
 * @author Alexander Weigl
 */
final class AskLlmRunner {

    private AskLlmRunner() {
    }

    /**
     * Runs the {@code ask_llm} tool call for the given tool arguments and returns the tool result
     * text (the fresh model's reply, or an explanatory error string) to be inserted into the
     * caller's thread.
     */
    static String run(LlmSession session, ChatCompletionsClient completions, String arguments) {
        var args = AgentTool.parseArgs(arguments);
        var prompt = AgentTool.stringArg(args, "prompt");
        if (prompt == null || prompt.isBlank()) {
            return "[ask_llm: the 'prompt' parameter must not be empty]";
        }
        var system = AgentTool.stringArg(args, "system");
        var model = AgentTool.stringArg(args, "model");
        if (model == null || model.isBlank()) {
            model = session.getModel();
        }

        var messages = new ArrayList<Map<String, Object>>();
        if (system != null && !system.isBlank()) {
            messages.add(Map.of("role", "system", "content", system));
        }
        messages.add(Map.of("role", "user", "content", prompt));

        var request = new AgentRequest(model, messages, List.of(), null, null, 1);
        try {
            var response = completions.complete(session, request);
            var message = AgentLoop.extractMessage(response);
            Object content = message.get("content");
            String text = content == null ? "" : String.valueOf(content).strip();
            if (text.isBlank()) {
                return "[ask_llm (model " + model + "): the model returned no content]";
            }
            return "[ask_llm (model " + model + "): fresh-context reply]\n\n" + text;
        } catch (Exception e) {
            return "[ask_llm failed: " + e.getMessage() + "]";
        }
    }
}
