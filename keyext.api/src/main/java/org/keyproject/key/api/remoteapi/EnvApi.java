/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.remoteapi;

import java.util.List;
import java.util.concurrent.CompletableFuture;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.proof.Proof;

import org.eclipse.lsp4j.jsonrpc.services.JsonRequest;
import org.eclipse.lsp4j.jsonrpc.services.JsonSegment;
import org.keyproject.key.api.data.ContractDesc;
import org.keyproject.key.api.data.SortDesc;

/**
 * @author Alexander Weigl
 * @version 1 (13.10.23)
 */
@JsonSegment("env")
public interface EnvApi {
    @JsonRequest
    CompletableFuture<List<SortDesc>> sorts(KeYEnvironment<?> env);

    @JsonRequest
    CompletableFuture<List<Function>> functions(KeYEnvironment<?> env);

    @JsonRequest
    CompletableFuture<List<ContractDesc>> contracts(KeYEnvironment<?> env);

    @JsonRequest
    CompletableFuture<Proof> openContract(KeYEnvironment<?> env, String contractId);
}
