/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.caching;

import java.nio.file.Path;

/**
 * A file used by some cached proof as part of the {@link CachingDatabase}.
 *
 * @param file path to the file (always located in ~/.key/cachedProofs)
 * @param hash {@link String#hashCode()} of this file's content
 * @author Arne Keller
 */
public record CachedFile(Path file, int hash) {
}
