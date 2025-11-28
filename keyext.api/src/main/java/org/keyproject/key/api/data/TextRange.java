/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.data;

/**
 * TextRange specifies a range of integer numbers e.g. character positions.
 *
 * @param start this range's (included) start position.
 * @param end this range's (excluded) end position.
 */
public record TextRange(int start, int end) implements KeYDataTransferObject {
}
