/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.data;


import org.keyproject.key.api.data.KeyIdentifications.NodeTextId;

/**
 * A printed sequent.
 *
 * @param id a handle identifying this print-out
 * @param result the plain textual notation of the sequent
 * @author Alexander Weigl
 * @version 1 (29.10.23)
 */
public record NodeTextDesc(NodeTextId id, String result)
        implements KeYDataTransferObject {
}
