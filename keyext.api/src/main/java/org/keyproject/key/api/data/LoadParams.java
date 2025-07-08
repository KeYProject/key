/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.data;

import java.nio.file.Path;
import java.util.List;

/**
 *
 * @param problemFile
 * @param classPath
 * @param bootClassPath
 * @param includes
 */
public record LoadParams(Path problemFile, List<Path> classPath, Path bootClassPath,
        List<Path> includes) implements KeYDataTransferObject {
}
