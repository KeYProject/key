/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.data;

import org.keyproject.key.api.data.KeyIdentifications.TermActionId;

/**
 * @author Alexander Weigl
 * @version 1 (13.10.23)
 */
public record TermActionDesc(TermActionId commandId, String displayName, String description,
        String category,
        TermActionKind kind) {
}
