/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.data;

import java.io.File;
import java.util.List;

/**
 *
 * @param keyFile
 * @param javaFile
 * @param classPath
 * @param bootClassPath
 * @param includes
 */
public record LoadParams(File problemFile, List<File> classPath, File bootClassPath,
        List<File> includes) implements KeYDataTransferObject {
}
