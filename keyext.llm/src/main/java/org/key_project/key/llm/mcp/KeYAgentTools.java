/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.ServiceLoader;
import java.util.TreeMap;
import java.util.function.Supplier;

import com.google.gson.GsonBuilder;
import org.jspecify.annotations.Nullable;

/**
 * The KeY-Agent's client side of the tool contract: a registry that aggregates every
 * {@link AgentTool} contributed by the {@link AgentToolProvider}s found on the class path
 * (Java {@link ServiceLoader}, service file
 * {@code META-INF/services/org.key_project.key.llm.mcp.AgentToolProvider}) and exposes them as
 * one {@link McpClient}.
 * <p>
 * The tool set is dynamic and modular by design:
 * <ul>
 * <li>each tool lives in its own provider class (see {@code org.key_project.key.llm.mcp.tools})
 * carrying its metadata (name, description, parameter schema, default approval) and its call
 * logic; the monolithic tool list + dispatch switch is gone,</li>
 * <li>plugins and test suites add tools by registering an {@link AgentToolProvider} - no change
 * to this class is needed,</li>
 * <li>the tool metadata is available programmatically via {@link #agents()} /
 * {@link #agent(String)},
 * as OpenAI-format definitions via {@link #getTools()} and rendered as Markdown via
 * {@link #toolsMarkdown()},</li>
 * <li>the tool set documents itself: {@code list_tools} ({@link #TOOL_LIST_TOOLS}) returns the
 * Markdown documentation of every registered tool.</li>
 * </ul>
 *
 * <p>
 * The built-in tools provided by {@code keyext.llm}:
 * <ul>
 * <li>{@code get_proof_context} - the current proof state as a text block</li>
 * <li>{@code glob} / {@code read} / {@code edit} - bounded, sandboxed access to the files of the
 * current Java model ({@code glob} matches glob patterns, {@code read} reads a bounded line
 * range, {@code edit} performs an exact string replacement and requires user approval)</li>
 * <li>{@code shell} - executes a shell command in the model directory (blocklist + user
 * approval required)</li>
 * <li>{@code question} - asks the user a question (intercepted by the agent loop)</li>
 * <li>{@code tryclose} - applies the {@code tryclose} proof-script command (TryClose macro) to a
 * goal, a branch or all open goals</li>
 * <li>{@code auto} - applies KeY's automatic proof strategy with a given step limit
 * (the {@code auto} proof-script command)</li>
 * <li>{@code list_proofs} - enumerates the open proofs with an identifier that the taclet tools
 * accept in their optional {@code proof} parameter</li>
 * <li>{@code list_taclets} / {@code list_taclet_options} / {@code export_taclet} - inspect the
 * taclets and taclet options of a proof, and export a taclet as parseable rule text</li>
 * <li>{@code export_taclets} - export several or all taclets of a proof as parseable rule text
 * (bounded output, optional filter)</li>
 * <li>{@code add_taclet} / {@code remove_taclet} - register a new taclet for a proof, resp. retire
 * one (future rule applications only; requires user approval)</li>
 * <li>{@code list_tools} - dumps the Markdown documentation of all tools</li>
 * </ul>
 *
 * @author Alexander Weigl
 */
public final class KeYAgentTools implements McpClient {

    public static final String TOOL_GET_PROOF_CONTEXT = "get_proof_context";
    public static final String TOOL_GLOB = "glob";
    public static final String TOOL_READ = "read";
    public static final String TOOL_EDIT = "edit";
    public static final String TOOL_SHELL = "shell";
    public static final String TOOL_QUESTION = "question";
    public static final String TOOL_SKILL = "skill";
    public static final String TOOL_SUBAGENT = "subagent";
    public static final String TOOL_GET_SUBAGENT_LOGS = "get_subagent_logs";
    /** Consults a fresh LLM instance with a clean context; intercepted by the agent loop. */
    public static final String TOOL_ASK_LLM = "ask_llm";
    public static final String TOOL_TRYCLOSE = "tryclose";
    public static final String TOOL_AUTO = "auto";
    public static final String TOOL_LIST_PROOFS = "list_proofs";
    public static final String TOOL_LIST_TACLETS = "list_taclets";
    public static final String TOOL_LIST_TACLET_OPTIONS = "list_taclet_options";
    public static final String TOOL_EXPORT_TACLET = "export_taclet";
    public static final String TOOL_EXPORT_TACLETS = "export_taclets";
    public static final String TOOL_ADD_TACLET = "add_taclet";
    public static final String TOOL_REMOVE_TACLET = "remove_taclet";
    public static final String TOOL_LIST_TOOLS = "list_tools";

    /** All registered tools, sorted by name (insertion order is otherwise load-order dependent). */
    private final TreeMap<String, AgentTool> tools = new TreeMap<>();

    public KeYAgentTools() {
        for (var provider : ServiceLoader.load(AgentToolProvider.class)) {
            for (var tool : provider.get()) {
                if (tool == null || tool.name() == null || tool.name().isBlank()) {
                    continue;
                }
                tools.putIfAbsent(tool.name(), tool);
            }
        }
        // The documentation tool sees the whole registry, including itself.
        tools.putIfAbsent(TOOL_LIST_TOOLS, new ToolsDocumentation(this::agents));
    }

    // ------------------------------------------------------------------- metadata access

    /**
     * All tools known to the registry (including the {@code list_tools} documentation tool),
     * sorted by name. This makes the tool metadata available programmatically; for the settings
     * UI use {@link BuiltInMCPClient#getAllTools()} instead, which also covers tools from other
     * MCP clients.
     */
    public List<AgentTool> agents() {
        return List.copyOf(new ArrayList<>(tools.values()));
    }

    /** The registered tool with the given name, or {@code null}. */
    public @Nullable AgentTool agent(String name) {
        return tools.get(name);
    }

    /** Renders the documentation of every registered tool as Markdown, grouped by category. */
    public String toolsMarkdown() {
        return buildToolsDocumentation(agents());
    }

    /** The full Markdown tool documentation (heading + approval legend + every tool block). */
    public String toolsDocumentation() {
        return buildToolsDocumentation(agents());
    }

    // ------------------------------------------------------------------- command line

    private static final String USAGE = "Usage: org.key_project.key.llm.mcp.KeYAgentTools [--json]";

    /**
     * CLI entry point: prints the tool documentation to stdout and exits. With {@code --json}
     * the OpenAI-format tool definitions (name, description, parameter schema) are printed
     * instead of the Markdown document. The registry is built headless, so no GUI or open proof
     * is required.
     */
    public static void main(String[] args) {
        boolean json = false;
        for (var arg : args) {
            switch (arg) {
                case "--json", "-j" -> json = true;
                case "--help", "-h" -> {
                    System.out.println(
                        "Prints the documentation of every tool available to the KeY-Agent.\n\n"
                            + USAGE + "\n  --json   print the OpenAI-format tool definitions"
                            + " instead of the Markdown document");
                    return;
                }
                default -> {
                    System.err.println("Unknown option: " + arg);
                    System.err.println(USAGE);
                    System.exit(2);
                }
            }
        }
        try {
            System.out.print(cliDocumentation(json));
        } catch (Exception e) {
            System.err.println("Failed to render the tool documentation: " + e.getMessage());
            System.exit(1);
        }
    }

    /**
     * Renders the CLI output (separated from {@link #main} so tests exercise it without starting
     * a second JVM): the Markdown tool documentation, or the OpenAI-format tool list as JSON.
     */
    static String cliDocumentation(boolean json) {
        var registry = new KeYAgentTools();
        if (json) {
            return new GsonBuilder().setPrettyPrinting().create()
                    .toJson(registry.agents().stream().map(AgentTool::asTool)
                            .map(KeYAgentTools::toolJson).toList());
        }
        return registry.toolsDocumentation();
    }

    /** The OpenAI-format map of a tool extended with the KeY-side category/background metadata. */
    private static Map<String, Object> toolJson(Tool tool) {
        var m = new java.util.LinkedHashMap<>(tool.toMap());
        m.put("category", tool.category().label());
        m.put("backgroundable", tool.backgroundable());
        return m;
    }

    // ------------------------------------------------------------------- McpClient

    @Override
    public List<Tool> getTools() {
        return agents().stream().map(AgentTool::asTool).toList();
    }

    @Override
    public Object callTool(String toolName, String arguments) throws Exception {
        var agent = tools.get(toolName);
        if (agent == null) {
            throw new IllegalArgumentException("unknown tool: " + toolName);
        }
        return agent.call(AgentTool.parseArgs(arguments));
    }

    @Override
    public boolean isClosed() {
        return false;
    }

    @Override
    public void close() {
    }

    // ------------------------------------------------------------------- documentation tool

    /**
     * The self-documenting {@code list_tools} tool: dumps the Markdown documentation of the
     * registered tools, filtered by {@code category} and/or {@code names}. It is registered
     * directly by {@link KeYAgentTools} (not via a provider) because it must observe the whole
     * registry.
     * <p>
     * The Proof and Taclet tools are only advertised to the model once this tool was called with
     * their {@code category} or {@code names}; the standard tools are always available.
     */
    private static final class ToolsDocumentation implements AgentTool {
        private final Supplier<List<AgentTool>> all;

        ToolsDocumentation(Supplier<List<AgentTool>> all) {
            this.all = all;
        }

        @Override
        public String name() {
            return TOOL_LIST_TOOLS;
        }

        @Override
        public ToolCategory category() {
            return ToolCategory.DOCUMENTATION;
        }

        @Override
        public JsonSchema parameters() {
            return AgentTool.schema(
                "category", JsonSchema.builder().withType("string")
                        .withDescription(
                            "Only document the KeY-specific tools of this category and "
                                + "load them for the following requests (\"proof\" or \"taclets\").")
                        .withEnum(List.of("proof", "taclets")).build(),
                "names", JsonSchema.builder().withType("array")
                        .withItems(JsonSchema.builder().withType("string").build())
                        .withDescription("Load exactly these KeY-specific tool names (proof and "
                            + "taclet tools) and document them.")
                        .build());
        }

        @Override
        public String description() {
            return "Dumps the Markdown documentation of the tools available to the agent - name,"
                + " approval requirement, description and parameters, including this tool"
                + " itself. The always-on standard tools (files, shell, skills, sub-agents) are"
                + " documented by default; the KeY-specific Proof and Taclet tools are kept out"
                + " of the request to keep it small and are only loaded (and documented) when"
                + " this tool is called with their category (\"proof\" or \"taclets\") or with"
                + " an explicit list of names. Call this tool first whenever you need to reason"
                + " about or change the proof.";
        }

        @Override
        public Object call(Map<String, Object> arguments) {
            var category = AgentTool.stringArg(arguments, "category");
            var names = namesArg(arguments);
            if (category != null || names != null) {
                return buildToolsDocumentation(all.get().stream()
                        .filter(t -> t.category().isKeySpecific())
                        .filter(t -> category == null
                                || t.category().name().equalsIgnoreCase(category.trim())
                                || t.category().label().equalsIgnoreCase(category.trim()))
                        .filter(t -> names == null || names.contains(t.name()))
                        .toList());
            }
            return buildToolsDocumentation(all.get());
        }

        private static @org.jspecify.annotations.Nullable List<String> namesArg(
                Map<String, Object> arguments) {
            Object v = arguments.get("names");
            if (!(v instanceof List<?> list) || list.isEmpty()) {
                return null;
            }
            return list.stream().map(String::valueOf).toList();
        }
    }

    /**
     * Renders the Markdown document describing the given tools (heading + legend + blocks),
     * grouped and sorted by {@link ToolCategory}.
     */
    private static String buildToolsDocumentation(List<AgentTool> toolList) {
        var sb = new StringBuilder();
        sb.append("# KeY-Agent tools\n\n");
        sb.append("All tools currently available to the agent.\n\n");
        sb.append("**Approval**: `AUTO` tools run without asking the user; `ASK` tools prompt"
            + " the user before the first execution in a turn. "
            + "**Background**: tools marked \u201ccan run in background\u201d may be moved to the"
            + " background while they run, so you can keep asking questions.\n\n");
        ToolCategory current = null;
        for (var tool : toolList.stream().sorted(byCategoryAndName()).toList()) {
            if (tool.category() != current) {
                current = tool.category();
                sb.append("## ").append(current.label()).append("\n\n");
            }
            sb.append(tool.toMarkdown()).append("\n\n");
        }
        return sb.toString().stripTrailing();
    }

    /** Sorts tools by category (declaration order) and then by name. */
    private static Comparator<AgentTool> byCategoryAndName() {
        return Comparator.comparing((AgentTool t) -> t.category().ordinal())
                .thenComparing(AgentTool::name);
    }
}
