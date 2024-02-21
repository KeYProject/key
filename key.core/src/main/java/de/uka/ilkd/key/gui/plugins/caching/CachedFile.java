/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.caching;

public final class CachedFile {
    /**
     * Name of this file. Always located in ~/.key/cachedProofs
     */
    public final String filename;
    public final int hash;

    public CachedFile(String filename, int hash) {
        this.filename = filename;
        this.hash = hash;
    }
}
