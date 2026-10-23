/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp;

import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.key.llm.ProofContextCollector;

import org.jspecify.annotations.Nullable;

/**
 * Shared helpers for tools that operate on the currently selected proof: access to the selected
 * proof/node, and the resolution of a tool's optional {@code proof} identifier (name or index as
 * listed by {@code list_proofs}) to an open proof.
 * <p>
 * Kept deliberately free of any Swing dependency beyond {@link MainWindow} so the resolution
 * logic ({@link #selectProof(List, Proof, String)}, {@link #proofsBlock(List, Proof)}) is
 * testable headless.
 *
 * @author Alexander Weigl
 */
public final class ProofSelector {

    private ProofSelector() {
    }

    /** A resolved tool target: either a proof or an error text to return to the model. */
    public record ProofRef(@Nullable Proof proof, @Nullable String error) {
    }

    /** The proof selected in the KeY GUI, or {@code null} when there is none. */
    public static @Nullable Proof selectedProof() {
        var mediator = MainWindow.getInstance() == null ? null
                : MainWindow.getInstance().getMediator();
        return mediator == null ? null : mediator.getSelectedProof();
    }

    /** The currently selected proof node, or {@code null}. */
    public static @Nullable Node selectedNode() {
        var mediator = MainWindow.getInstance() == null ? null
                : MainWindow.getInstance().getMediator();
        return mediator == null ? null : mediator.getSelectedNode();
    }

    /** The canonical name of a proof (also used by {@code list_proofs}). */
    public static String proofName(Proof proof) {
        return ProofContextCollector.proofName(proof);
    }

    /**
     * Resolves the target proof of a tool call: the optional {@code proof} parameter (name or
     * index as listed by {@code list_proofs}), or the currently selected proof if omitted.
     */
    public static ProofRef proofRef(Map<String, Object> args) {
        var mediator = MainWindow.getInstance() == null ? null
                : MainWindow.getInstance().getMediator();
        var selected = mediator == null ? null : mediator.getSelectedProof();
        var opened = mediator == null ? List.<Proof>of() : mediator.getCurrentlyOpenedProofs();
        return selectProof(opened, selected, AgentTool.stringArg(args, "proof"));
    }

    /**
     * Selects a proof from the opened proofs by identifier: an exact (or case-insensitive) proof
     * name, or the 0-based index shown by {@code list_proofs}. Without an identifier the selected
     * proof is used.
     */
    public static ProofRef selectProof(List<Proof> opened, @Nullable Proof selected,
            @Nullable String id) {
        if (id == null || id.isBlank()) {
            return selected != null ? new ProofRef(selected, null)
                    : new ProofRef(null,
                        "Error: no proof selected; pass a 'proof' identifier from list_proofs");
        }
        Integer index = null;
        try {
            index = Integer.valueOf(id.trim());
        } catch (NumberFormatException ignored) {
        }
        if (index != null) {
            if (index < 0 || index >= opened.size()) {
                return new ProofRef(null, "Error: proof index " + index + " is out of range [0,"
                    + Math.max(0, opened.size() - 1) + "]; call list_proofs");
            }
            return new ProofRef(opened.get(index), null);
        }
        var matches = opened.stream().filter(p -> id.equals(proofName(p))).toList();
        if (matches.size() != 1) {
            matches = opened.stream().filter(p -> id.equalsIgnoreCase(proofName(p))).toList();
        }
        if (matches.size() == 1) {
            return new ProofRef(matches.get(0), null);
        }
        if (matches.isEmpty()) {
            return new ProofRef(null,
                "Error: no open proof named \"" + id + "\"; call list_proofs");
        }
        return new ProofRef(null, "Error: \"" + id + "\" matches " + matches.size()
            + " open proofs; use the index shown by list_proofs instead");
    }

    /**
     * Renders the {@code list_proofs} result for the open proofs, marking the selected one.
     */
    public static String proofsBlock(List<Proof> opened, @Nullable Proof selected) {
        if (opened.isEmpty()) {
            return "(no proofs are open)";
        }
        var sb = new StringBuilder();
        for (int i = 0; i < opened.size(); i++) {
            var proof = opened.get(i);
            int openGoals = proof.openGoals().size();
            sb.append(i).append(": ").append(proofName(proof)).append(" — ").append(openGoals)
                    .append(openGoals == 0 ? " (closed)" : " open goal(s)")
                    .append(proof == selected ? " [selected]" : "").append("\n");
        }
        sb.append("Pass the name or the index as the 'proof' parameter of the taclet tools.");
        return sb.toString().stripTrailing();
    }
}
