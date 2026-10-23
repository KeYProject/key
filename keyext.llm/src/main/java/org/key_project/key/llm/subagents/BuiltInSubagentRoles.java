/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.subagents;

import java.util.List;

import org.key_project.key.llm.mcp.KeYAgentTools;

/**
 * The built-in sub-agent roles ({@code goal-solver}, {@code file-explorer},
 * {@code rule-designer}). Each role couples a focused system prompt with a conservative tool
 * whitelist, so a sub-agent can only do what its role was designed for:
 * <ul>
 * <li>{@code goal-solver} works on the current proof with the automatic strategies; it cannot
 * run commands or mutate the rule set,</li>
 * <li>{@code file-explorer} inspects the files of the current Java model (read-only),</li>
 * <li>{@code rule-designer} designs and registers taclets (mutating: sequential only).</li>
 * </ul>
 * Roles are tools-free by themselves - they only whitelist tools that already exist in the tool
 * set; {@code spawn_subagent} itself is never whitelisted implicitly.
 *
 * @author Alexander Weigl
 */
public final class BuiltInSubagentRoles implements SubagentRoleProvider {

    @Override
    public List<SubagentRole> get() {
        return List.of(
            new SubagentRole("goal-solver",
                "Solves goals of the current proof with the automatic strategies.",
                "You solve goals of KeY proofs. Inspect the current goal sequent first, then pick "
                    + "a strategy: apply the automatic strategy with a suitable number of steps, "
                    + "or close goals directly. List the open proofs and report which goals you "
                    + "closed. Never change the rule set and never run shell commands.",
                List.of(KeYAgentTools.TOOL_GET_PROOF_CONTEXT, KeYAgentTools.TOOL_LIST_PROOFS,
                    KeYAgentTools.TOOL_TRYCLOSE, KeYAgentTools.TOOL_AUTO,
                    KeYAgentTools.TOOL_LIST_TACLETS),
                null, 10, true),
            new SubagentRole("file-explorer",
                "Explores the files of the current Java model (read-only).",
                "You inspect source files of the current Java model. List the model files, read "
                    + "the relevant ones and report method signatures, JML annotations and "
                    + "invariants that matter for the task. Do not modify anything.",
                List.of(KeYAgentTools.TOOL_LIST_FILES, KeYAgentTools.TOOL_READ_FILE,
                    KeYAgentTools.TOOL_FILE_INFO),
                null, 6, true),
            new SubagentRole("rule-designer",
                "Designs KeY rules (taclets) for the current proof.",
                "You design KeY rules (taclets) for the current proof. Inspect the existing rules "
                    + "and options, then propose or register a taclet. Verify the taclet with "
                    + "export and clean up when it does not help. Do not use shell commands.",
                List.of(KeYAgentTools.TOOL_LIST_PROOFS, KeYAgentTools.TOOL_LIST_TACLETS,
                    KeYAgentTools.TOOL_LIST_TACLET_OPTIONS, KeYAgentTools.TOOL_EXPORT_TACLET,
                    KeYAgentTools.TOOL_EXPORT_TACLETS, KeYAgentTools.TOOL_ADD_TACLET,
                    KeYAgentTools.TOOL_REMOVE_TACLET),
                null, 8, false));
    }
}
