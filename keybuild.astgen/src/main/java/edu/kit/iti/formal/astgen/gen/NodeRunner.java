/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package edu.kit.iti.formal.astgen.gen;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import com.palantir.javapoet.ClassName;
import com.palantir.javapoet.JavaFile;
import com.palantir.javapoet.TypeSpec;
import edu.kit.iti.formal.astgen.model.Node;

/**
 * @author Alexander Weigl
 * @version 1 (10.09.17)
 */
public class NodeRunner extends AbstractRunner {
    private final List<NodeGenerator> generatorsUnit = new ArrayList<>();

    @Override
    public void process() {
        for (Node node : getHierarchy().nodes()) {
            var type = TypeSpec.classBuilder(
                ClassName.get(node.pckg(), node.name()));

            for (NodeGenerator generator : generatorsUnit) {
                type = generator.modify(node, type);
            }

            for (NodeGenerator gen : generatorsUnit) {
                gen.setHierarchy(hierarchy);
                type = gen.modify(node, type);
            }
            var t = type.build();
            var jf = JavaFile.builder(node.pckg(), t).build();
            try {
                jf.writeToPath(sourceDirectory);
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        }
    }

    public List<NodeGenerator> getGeneratorsUnit() {
        return generatorsUnit;
    }
}
