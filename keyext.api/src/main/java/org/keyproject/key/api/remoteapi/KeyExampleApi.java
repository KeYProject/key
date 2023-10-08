/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.remoteapi;

import java.util.List;
import java.util.concurrent.CompletableFuture;

import de.uka.ilkd.key.gui.Example;

import org.eclipse.lsp4j.jsonrpc.services.JsonRequest;
import org.eclipse.lsp4j.jsonrpc.services.JsonSegment;

@JsonSegment("examples")
public interface KeyExampleApi {
    @JsonRequest("list")
    CompletableFuture<List<Example>> examples();
}
