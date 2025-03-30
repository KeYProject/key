/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package edu.kit.iti.formal.astgen.runner;

import com.palantir.javapoet.TypeSpec;
import edu.kit.iti.formal.astgen.model.Node;

/**
 * @author Alexander Weigl
 * @version 1 (12.10.17)
 */
public class FileHeader extends AbstractNodeGenerator {
    public String comment;

    @Override
    public TypeSpec.Builder modify(Node node, TypeSpec.Builder unit) {
        unit.addJavadoc(comment.trim());
        return unit;
    }
}
