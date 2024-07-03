/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package org.key_project.ui.interactionlog.api;

/**
 * @author Alexander Weigl
 * @version 1 (08.05.19)
 */
public interface Markdownable {
    default String getMarkdown() {
        return String.format("**Unsupported interaction: %s**%n%n", this.getClass().getName());
    }
}
