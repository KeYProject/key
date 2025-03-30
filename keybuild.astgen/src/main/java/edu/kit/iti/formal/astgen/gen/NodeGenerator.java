/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package edu.kit.iti.formal.astgen.gen;

import com.palantir.javapoet.TypeSpec;
import edu.kit.iti.formal.astgen.model.Hierarchy;
import edu.kit.iti.formal.astgen.model.Node;

/**
 * @author Alexander Weigl
 * @version 1 (10.09.17)
 */
public interface NodeGenerator {
    void setHierarchy(Hierarchy h);

    TypeSpec.Builder modify(Node node, TypeSpec.Builder unit);
}
