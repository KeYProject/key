/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules;

import org.jspecify.annotations.Nullable;

/// Collection of attributes for taclets.
public record TacletAttributes(@Nullable String displayName, @Nullable Trigger trigger) {
}
