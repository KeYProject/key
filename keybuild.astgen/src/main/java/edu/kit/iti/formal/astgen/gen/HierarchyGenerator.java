/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package edu.kit.iti.formal.astgen.gen;

import java.nio.file.Path;
import java.util.List;

import com.palantir.javapoet.JavaFile;
import edu.kit.iti.formal.astgen.model.Hierarchy;

/**
 * @author Alexander Weigl
 * @version 1 (10.09.17)
 */
public interface HierarchyGenerator {
    List<JavaFile> modify(Path sourceFolder, Hierarchy hierarchy);
}
