/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api;

import java.util.List;
import java.util.concurrent.CompletableFuture;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.gui.Example;
import de.uka.ilkd.key.gui.ExampleChooser;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFacade;
import de.uka.ilkd.key.macros.scripts.ProofScriptCommand;
import de.uka.ilkd.key.macros.scripts.ProofScriptCommandFacade;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.Statistics;
import de.uka.ilkd.key.util.KeYConstants;

import org.eclipse.lsp4j.jsonrpc.CompletableFutures;
import org.eclipse.lsp4j.jsonrpc.services.JsonRequest;
import org.keyproject.key.api.adapters.KeyAdapter;
import org.keyproject.key.api.data.*;
import org.keyproject.key.api.remoteapi.KeyApi;

public record KeyApiImpl(KeyAdapter adapter) implements KeyApi {

    @Override
    @JsonRequest
    public CompletableFuture<List<Example>> examples() {
        return CompletableFutures
                .computeAsync((c) -> ExampleChooser.listExamples(ExampleChooser.lookForExamples()));
    }

    @Override
    public CompletableFuture<Void> shutdown() {
        return CompletableFuture.completedFuture(null);
    }

    @Override
    public void exit() {
    }

    @Override
    public void setTrace(SetTraceParams params) {

    }

    @Override
    public CompletableFuture<String> getVersion() {
        return CompletableFuture.completedFuture(KeYConstants.VERSION);
    }

    @Override
    public CompletableFuture<List<ProofMacro>> getAvailableMacros() {
        return CompletableFuture.completedFuture(
            ProofMacroFacade.instance().getMacros().stream().toList());
    }

    @Override
    public CompletableFuture<List<ProofScriptCommand<?>>> getAvailableScriptCommands() {
        return CompletableFuture.completedFuture(
            ProofScriptCommandFacade.instance().getScriptCommands().stream().toList());
    }

    @Override
    public CompletableFuture<MacroStatistic> script(Proof proof, String scriptLine,
            StreategyOptions options) {
        return null;
    }

    @Override
    public CompletableFuture<MacroStatistic> macro(Proof id, String macroId,
            StreategyOptions options) {
        return null;
    }

    @Override
    public CompletableFuture<MacroStatistic> auto(Proof id, StreategyOptions options) {
        return null;
    }

    @Override
    public CompletableFuture<Boolean> dispose(Proof id) {
        return null;
    }

    @Override
    public CompletableFuture<NodeDesc> goals(Proof id) {
        return null;
    }

    @Override
    public CompletableFuture<NodeDesc> tree(Proof proof) {
        return null;
    }

    @Override
    public CompletableFuture<NodeDesc> root(Proof proof) {
        return null;
    }

    @Override
    public CompletableFuture<List<NodeDesc>> children(Proof proof, Node nodeId) {
        return null;
    }

    @Override
    public CompletableFuture<List<NodeDesc>> pruneTo(Proof proof, Node nodeId) {
        return null;
    }

    @Override
    public CompletableFuture<Statistics> statistics(Proof proof) {
        return null;
    }

    @Override
    public CompletableFuture<TreeNodeDesc> treeRoot(Proof proof) {
        return null;
    }

    @Override
    public CompletableFuture<List<TreeNodeDesc>> treeChildren(Proof proof, TreeNodeId nodeId) {
        return null;
    }

    @Override
    public CompletableFuture<List<TreeNodeDesc>> treeSubtree(Proof proof, TreeNodeId nodeId) {
        return null;
    }

    @Override
    public CompletableFuture<List<SortDesc>> sorts(KeYEnvironment<?> env) {
        return null;
    }

    @Override
    public CompletableFuture<List<Function>> functions(KeYEnvironment<?> env) {
        return null;
    }

    @Override
    public CompletableFuture<List<ContractDesc>> contracts(KeYEnvironment<?> env) {
        return null;
    }

    @Override
    public CompletableFuture<Proof> openContract(KeYEnvironment<?> env, String contractId) {
        return null;
    }

    @Override
    public CompletableFuture<GoalText> print(Node id) {
        return null;
    }

    @Override
    public CompletableFuture<List<TermAction>> actions(PrintId id, int pos) {
        return null;
    }

    @Override
    public CompletableFuture<List<TermAction>> applyAction(TermActionId id) {
        return null;
    }

    @Override
    public void freePrint(PrintId id) {

    }
}
