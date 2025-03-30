/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package edu.kit.iti.formal.astgen.model;

import org.jspecify.annotations.Nullable;

public class NodeWrapper {
    private @Nullable Node node;

    public @Nullable Node node() {
        return node;
    }

    public void setNode(Node node) {
        this.node = node;
    }
}
