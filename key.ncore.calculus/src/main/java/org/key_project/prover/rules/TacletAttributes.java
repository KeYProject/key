/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/// Collection of attributes for taclets.
/// @param displayName if present a usually shorter but not necessary unique name; otherwise the
/// name of the taclet
/// @param trigger a condition signalling whether an applicable taclet should be applied by the
/// strategies or avoided
/// (this condition does not effect soundness, the taclet must be sound irrespective of the trigger)
public record TacletAttributes(@NonNull String displayName, @Nullable Trigger trigger) {
}
