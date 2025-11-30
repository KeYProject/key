/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.remoteapi;

import java.util.List;
import java.util.concurrent.CompletableFuture;

import org.eclipse.lsp4j.jsonrpc.services.JsonRequest;
import org.eclipse.lsp4j.jsonrpc.services.JsonSegment;
import org.keyproject.key.api.data.ExampleDesc;
import org.keyproject.key.api.data.KeyIdentifications;

/**
 * Management of the built-in examples of KeY.
 *
 * @author weigl
 */
@JsonSegment("examples")
public interface ExampleApi {
    /**
     * A list of examples that are built-in into KeY.
     *
     * @return a list of examples descriptions
     */
    @JsonRequest("list")
    CompletableFuture<List<ExampleDesc>> examples();

    /**
     * I am not sure whether this is helpful. Mainly a feature for testing?!
     *
     * @param name of the example
     * @return opens a new proof returns a handle
     * @see ExampleDesc#name()
     */
    @JsonRequest
    CompletableFuture<KeyIdentifications.ProofId> loadExample(String name);
}
