/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.remoteapi;

/**
 * The combined interface that is provided by KeY.
 */
public interface KeyApi extends
        ExampleApi,
        MetaApi,
        ServerManagement,
        ProofApi,
        ProofTreeApi,
        GoalApi,
        EnvApi,
        ProofLoadApi {
}
