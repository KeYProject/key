/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api;

import org.keyproject.key.api.data.KeyIdentifications.NodeId;

/**
 * @author Alexander Weigl
 * @version 1 (29.10.23)
 */
public record NodeTextId(NodeId nodeId, int nodeTextId) {
}
