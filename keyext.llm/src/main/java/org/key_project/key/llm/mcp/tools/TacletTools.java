/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp.tools;

import java.util.List;

import org.key_project.key.llm.TacletOperations;
import org.key_project.key.llm.mcp.AgentTool;
import org.key_project.key.llm.mcp.AgentToolProvider;
import org.key_project.key.llm.mcp.JsonSchema;
import org.key_project.key.llm.mcp.KeYAgentTools;
import org.key_project.key.llm.mcp.ProofSelector;
import org.key_project.key.llm.mcp.Tool;

/**
 * The taclet-management tools ({@code list_taclets}, {@code list_taclet_options},
 * {@code export_taclet}, {@code export_taclets}, {@code add_taclet}, {@code remove_taclet}):
 * they inspect and modify the rule set of a proof (see {@link TacletOperations}). The optional
 * {@code proof} parameter addresses a proof by the identifier returned by {@code list_proofs};
 * omitting it targets the currently selected proof.
 *
 * @author Alexander Weigl
 */
public final class TacletTools implements AgentToolProvider {
    @Override
    public List<AgentTool> get() {
        var proofParam = JsonSchema.builder().withType("string")
                .withDescription("proof identifier (name or index) as returned by list_proofs;"
                    + " omit to use the currently selected proof")
                .build();
        return List.of(
            AgentTool.tool(KeYAgentTools.TOOL_LIST_TACLETS,
                "Lists the taclets (rewrite and apply rules) available for a proof, one name per"
                    + " line. Optionally filters by a case-insensitive substring.",
                AgentTool.schema("proof", proofParam,
                    "filter", JsonSchema.builder().withType("string")
                            .withDescription("optional case-insensitive substring to filter"
                                + " taclet names")
                            .build()),
                args -> {
                    var ref = ProofSelector.proofRef(args);
                    return ref.error() != null ? ref.error()
                            : TacletOperations.listTaclets(ref.proof(),
                                AgentTool.stringArg(args, "filter"));
                }),
            AgentTool.tool(KeYAgentTools.TOOL_LIST_TACLET_OPTIONS,
                "Lists the taclet options (choices) of a proof: the selected value of each option"
                    + " category such as programRules, together with the possible values.",
                AgentTool.schema("proof", proofParam),
                args -> {
                    var ref = ProofSelector.proofRef(args);
                    return ref.error() != null ? ref.error()
                            : TacletOperations.listTacletOptions(ref.proof());
                }),
            AgentTool.tool(KeYAgentTools.TOOL_EXPORT_TACLET,
                "Exports a taclet of a proof as a parseable KeY rule declaration. The text can be"
                    + " edited and registered again with add_taclet.",
                AgentTool.schema("proof", proofParam,
                    "taclet", JsonSchema.builder().withType("string")
                            .withDescription("name of the taclet to export")
                            .build()),
                args -> {
                    var ref = ProofSelector.proofRef(args);
                    if (ref.error() != null) {
                        return ref.error();
                    }
                    var name = AgentTool.stringArg(args, "taclet");
                    return name == null || name.isBlank()
                            ? "Error: 'taclet' parameter is required"
                            : TacletOperations.exportTaclet(ref.proof(), name);
                }),
            AgentTool.tool(KeYAgentTools.TOOL_EXPORT_TACLETS,
                "Exports several taclets of a proof as parseable KeY rule declarations,"
                    + " optionally filtered by a case-insensitive substring; without a filter all"
                    + " available taclets are exported. The output is capped: narrow it with"
                    + " 'filter' if the result is truncated, or export single taclets with"
                    + " export_taclet.",
                AgentTool.schema("proof", proofParam,
                    "filter", JsonSchema.builder().withType("string")
                            .withDescription("optional case-insensitive substring to filter"
                                + " taclet names")
                            .build()),
                args -> {
                    var ref = ProofSelector.proofRef(args);
                    return ref.error() != null ? ref.error()
                            : TacletOperations.exportTaclets(ref.proof(),
                                AgentTool.stringArg(args, "filter"));
                }),
            AgentTool.tool(KeYAgentTools.TOOL_ADD_TACLET,
                "Registers a new taclet for a proof, given as a parseable KeY rule declaration"
                    + " (\\taclet <name> { ... };). The taclet becomes available for future rule"
                    + " applications of that proof. Requires user approval.",
                Tool.ApprovalRequirement.ASK,
                AgentTool.schema("proof", proofParam,
                    "taclet", JsonSchema.builder().withType("string")
                            .withDescription("the taclet declaration text, e.g."
                                + " \\taclet my_rule { ... };")
                            .build()),
                args -> {
                    var ref = ProofSelector.proofRef(args);
                    if (ref.error() != null) {
                        return ref.error();
                    }
                    var source = AgentTool.stringArg(args, "taclet");
                    return source == null || source.isBlank()
                            ? "Error: 'taclet' parameter is required"
                            : TacletOperations.addTaclet(ref.proof(), source);
                }),
            AgentTool.tool(KeYAgentTools.TOOL_REMOVE_TACLET,
                "Removes a taclet from a proof's rule set so that it is no longer offered for"
                    + " future rule applications. Rule applications that already happened are not"
                    + " affected. Requires user approval.",
                Tool.ApprovalRequirement.ASK,
                AgentTool.schema("proof", proofParam,
                    "taclet", JsonSchema.builder().withType("string")
                            .withDescription("name of the taclet to remove")
                            .build()),
                args -> {
                    var ref = ProofSelector.proofRef(args);
                    if (ref.error() != null) {
                        return ref.error();
                    }
                    var name = AgentTool.stringArg(args, "taclet");
                    return name == null || name.isBlank()
                            ? "Error: 'taclet' parameter is required"
                            : TacletOperations.removeTaclet(ref.proof(), name);
                }));
    }
}
