/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.key.llm;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.key.llm.AgentResult.Question;
import org.key_project.key.llm.AgentResult.ToolActivity;
import org.key_project.key.llm.AgentResult.ToolCallInfo;
import org.key_project.key.llm.LlmContext.LlmMessage;
import org.key_project.key.llm.mcp.KeYAgentTools;

import com.google.gson.GsonBuilder;
import org.jspecify.annotations.Nullable;

/**
 * The KeY-Agent driver: runs one conversation turn as a bounded tool-calling loop and pauses for
 * user interaction (questions and tool approvals).
 * <p>
 * Life cycle:
 * <ol>
 * <li>{@link #begin begin(...)} runs until a final answer ({@link AgentResult.Done}), a question
 * ({@link AgentResult.NeedsInput}), an approval request ({@link AgentResult.NeedsApproval})
 * or an error ({@link AgentResult.Failed}) occurs.</li>
 * <li>On a question, the UI shows it and calls {@link #answerQuestion(String)}.</li>
 * <li>On an approval request, the UI asks the user and calls
 * {@link #decideApproval(boolean, boolean)}.</li>
 * </ol>
 * All assistant/tool messages of one turn are appended to the session's per-proof
 * {@link LlmSession#getContext() context} while they occur, so the next turn continues naturally.
 * The number of tool rounds is bounded by {@code maxToolRounds}.
 *
 * @author Alexander Weigl
 */
public class AgentLoop {
    private final LlmSession session;
    private final ChatCompletionsClient completions;

    private final List<Map<String, Object>> thread = new ArrayList<>();
    private final List<ToolActivity> activities = new ArrayList<>();
    private AgentRequest request;
    private int rounds = 0;
    private boolean cancelled = false;
    private @Nullable Pending pending;

    private interface Pending {
    }

    private record PendingApproval(String toolCallId, String name, String arguments)
            implements Pending {
    }

    private record PendingQuestion(String toolCallId, Question question) implements Pending {
    }

    public AgentLoop(LlmSession session, ChatCompletionsClient completions) {
        this.session = session;
        this.completions = completions;
    }

    /**
     * Starts a new turn with the given raw user input. Resolves {@code $}, {@code @} and
     * {@code /} markup, assembles the request and runs the loop.
     */
    public AgentResult begin(String rawUserText, @Nullable Proof proof, @Nullable Node node,
            @Nullable Skill skill) {
        var resolver = new PromptResolver.Context() {
            @Override
            public @Nullable Proof proof() {
                return proof;
            }

            @Override
            public @Nullable Node node() {
                return node;
            }
        };
        var resolved = PromptResolver.resolve(rawUserText, session, resolver);

        // /skill: directive of this message wins; otherwise the session's active skill applies
        Skill effective =
            resolved.skillName() != null ? SkillLibrary.INSTANCE.get(resolved.skillName())
                    : skill;
        request = ExtendedPrompt.build(session, proof, node, resolved.text(), effective);
        thread.clear();
        thread.addAll(request.messages());
        activities.clear();
        rounds = 0;
        cancelled = false;
        pending = null;
        return loop();
    }

    /** Continues the turn after the user answered a question. */
    public AgentResult answerQuestion(String answer) {
        if (!(pending instanceof PendingQuestion q)) {
            return new AgentResult.Failed(new IllegalStateException("no pending question"));
        }
        pending = null;
        addToolResult(q.toolCallId(), "Answer: " + answer, false);
        return loop();
    }

    /**
     * Continues the turn after an approval decision.
     *
     * @param allow whether the tool may run
     * @param always remember the decision without further prompts for this tool
     */
    public AgentResult decideApproval(boolean allow, boolean always) {
        if (!(pending instanceof PendingApproval p)) {
            return new AgentResult.Failed(new IllegalStateException("no pending approval"));
        }
        pending = null;
        if (!allow) {
            addToolResult(p.toolCallId(),
                "[Tool call denied by the user: " + p.name() + "]", false);
            return loop();
        }
        if (always) {
            session.getMcpClient().allowWithoutApproval(p.name());
        }
        try {
            var result = session.getMcpClient().callTool(p.name(), p.arguments());
            addToolResult(p.toolCallId(), stringify(result), true);
        } catch (Exception e) {
            addToolResult(p.toolCallId(), "Error: " + e.getMessage(), false);
        }
        return loop();
    }

    /** Requests cancellation; takes effect after the current HTTP call returns. */
    public void cancel() {
        cancelled = true;
    }

    public boolean isCancelled() {
        return cancelled;
    }

    public boolean hasPendingQuestion() {
        return pending instanceof PendingQuestion;
    }

    public boolean hasPendingApproval() {
        return pending instanceof PendingApproval;
    }

    /** Whether a tool-calling round is in progress (used to enable/disable the stop button). */
    public boolean isRunning() {
        return !cancelled && pending == null;
    }

    // --------------------------------------------------------------------- core loop

    private AgentResult loop() {
        int maxRounds = Math.max(1, request.maxToolRounds());
        while (true) {
            if (cancelled || Thread.currentThread().isInterrupted()) {
                return new AgentResult.Done("(Turn cancelled by the user.)",
                    List.copyOf(activities));
            }
            if (rounds >= maxRounds) {
                return new AgentResult.Done(
                    "(Stopped: the maximum number of tool rounds (" + maxRounds
                        + ") was reached without a final answer.)",
                    List.copyOf(activities));
            }

            final Map<String, Object> response;
            try {
                response = completions.complete(session, new AgentRequest(request.model(),
                    List.copyOf(thread), request.tools(), request.temperature(),
                    request.maxOutputTokens(), request.maxToolRounds()));
            } catch (Exception e) {
                return new AgentResult.Failed(e);
            }

            final Map<?, ?> message;
            try {
                message = extractMessage(response);
            } catch (Exception e) {
                return new AgentResult.Failed(e);
            }

            var toolCalls = asList(message.get("tool_calls"));
            String content = message.get("content") == null ? ""
                    : String.valueOf(message.get("content"));

            if (toolCalls == null || toolCalls.isEmpty()) {
                var answer = new LlmMessage("assistant", content);
                session.getContext().addMessage(answer);
                return new AgentResult.Done(content, List.copyOf(activities));
            }

            rounds++;
            var assistantMsg = LlmMessage.assistant(content, casts(toolCalls));
            thread.add(assistantMsg.toOpenAiMap());
            session.getContext().addMessage(assistantMsg);

            var interrupted = processBatch(casts(toolCalls));
            if (interrupted != null) {
                return interrupted; // NEEDS_INPUT or NEEDS_APPROVAL
            }
            // otherwise the batch results were appended to the thread; loop with the follow-up
        }
    }

    /**
     * Executes a batch of tool calls. Returns a non-null result when the turn must pause for the
     * user; {@code null} when the turn can continue with the collected tool results.
     */
    private @Nullable AgentResult processBatch(List<Map<String, Object>> toolCalls) {
        var results = new ArrayList<LlmMessage>();
        for (var toolCall : toolCalls) {
            var id = String.valueOf(toolCall.get("id"));
            Object func = toolCall.get("function");
            var function = func instanceof Map<?, ?> f ? f : Map.of();
            var name = String.valueOf(function.get("name"));
            var arguments = function.get("arguments") == null ? "{}"
                    : String.valueOf(function.get("arguments"));

            if (KeYAgentTools.TOOL_ASK_USER.equals(name)) {
                if (!LlmSettings.INSTANCE.getAllowAgentQuestions()) {
                    results.add(LlmMessage.tool(id,
                        "[Asking the user is disabled in the settings]"));
                    continue;
                }
                flush(results);
                var question = parseQuestion(arguments);
                pending = new PendingQuestion(id, question);
                return new AgentResult.NeedsInput(question);
            }

            if (KeYAgentTools.TOOL_USE_SKILL.equals(name)) {
                if (!LlmSettings.INSTANCE.getAgentCanUseSkills()) {
                    results.add(LlmMessage.tool(id, "[Skills are disabled in the settings]"));
                    continue;
                }
                var skillName = parseSkillName(arguments);
                if (skillName == null || SkillLibrary.INSTANCE.get(skillName) == null) {
                    results.add(LlmMessage.tool(id,
                        "[Unknown skill: " + (skillName == null ? "(missing name)" : skillName)
                            + "]"));
                    continue;
                }
                session.setActiveSkill(skillName);
                results.add(LlmMessage.tool(id,
                    "[Skill '" + skillName + "' activated for subsequent turns]"));
                continue;
            }

            if (session.getMcpClient().requiresApproval(name)) {
                flush(results);
                pending = new PendingApproval(id, name, arguments);
                return new AgentResult.NeedsApproval(new ToolCallInfo(id, name, arguments));
            }

            try {
                var result = session.getMcpClient().callTool(name, arguments);
                results.add(LlmMessage.tool(id, stringify(result)));
                activities.add(new ToolActivity(name, arguments, stringify(result)));
            } catch (Exception e) {
                var errorText = "Error calling " + name + ": " + e.getMessage();
                results.add(LlmMessage.tool(id, errorText));
                activities.add(new ToolActivity(name, arguments, errorText));
            }
        }
        flush(results);
        return null;
    }

    private void flush(List<LlmMessage> results) {
        for (var msg : results) {
            thread.add(msg.toOpenAiMap());
            session.getContext().addMessage(msg);
        }
        results.clear();
    }

    private void addToolResult(String toolCallId, String content, boolean asActivity) {
        var msg = LlmMessage.tool(toolCallId, content);
        thread.add(msg.toOpenAiMap());
        session.getContext().addMessage(msg);
    }

    private static Question parseQuestion(String arguments) {
        try {
            var parsed = new GsonBuilder().create().fromJson(arguments, Question.class);
            return parsed == null ? new Question(arguments, List.of()) : parsed;
        } catch (Exception e) {
            return new Question(arguments, List.of());
        }
    }

    private static @Nullable String parseSkillName(String arguments) {
        try {
            var parsed = new GsonBuilder().create().fromJson(arguments, Map.class);
            if (parsed != null) {
                Object name = parsed.get("name");
                return name == null ? null : String.valueOf(name);
            }
        } catch (Exception e) {
            // fall through
        }
        return null;
    }

    private static Map<?, ?> extractMessage(Map<String, Object> response) throws Exception {
        var choices = asList(response.get("choices"));
        if (choices == null || choices.isEmpty()) {
            throw new RuntimeException("The API response contains no choices.");
        }
        Object first = choices.get(0);
        if (!(first instanceof Map<?, ?> choice)) {
            throw new RuntimeException("Malformed choice in API response.");
        }
        Object message = choice.get("message");
        if (!(message instanceof Map<?, ?> m)) {
            throw new RuntimeException("Malformed message in API response.");
        }
        return m;
    }

    private static String stringify(Object result) {
        if (result == null) {
            return "(no result)";
        }
        if (result instanceof String s) {
            return s;
        }
        try {
            return new GsonBuilder().create().toJson(result);
        } catch (Exception e) {
            return result.toString();
        }
    }

    @SuppressWarnings("unchecked")
    private static List<Map<String, Object>> casts(List<?> toolCalls) {
        List<Map<String, Object>> result = new ArrayList<>();
        for (Object o : toolCalls) {
            if (o instanceof Map<?, ?> m) {
                result.add((Map<String, Object>) m);
            }
        }
        return result;
    }

    @SuppressWarnings("unchecked")
    private static List<?> asList(Object o) {
        return o instanceof List<?> l ? l : null;
    }
}
