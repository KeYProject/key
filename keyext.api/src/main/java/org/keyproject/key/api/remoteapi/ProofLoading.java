/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.remoteapi;

import de.uka.ilkd.key.proof.io.ProblemLoaderException;

import org.eclipse.lsp4j.jsonrpc.services.JsonRequest;
import org.eclipse.lsp4j.jsonrpc.services.JsonSegment;

@JsonSegment
public interface ProofLoading {
    @JsonRequest
    ProofId loadExample(String id);

    /**
     * @param params
     * @return
     * @throws ProblemLoaderException
     */
    @JsonRequest
    EnvId load(LoadParams params) throws ProblemLoaderException;
}
