/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.remoteapi;

/**
 * @author Alexander Weigl
 * @version 1 (29.10.23)
 */
public record PrintOptions(boolean unicode, int width, int indentation, boolean pure,
        boolean termLabels) {
}
