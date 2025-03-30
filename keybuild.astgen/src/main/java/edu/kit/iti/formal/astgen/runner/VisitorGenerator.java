/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package edu.kit.iti.formal.astgen.runner;

import java.nio.file.Path;
import java.util.List;
import java.util.stream.IntStream;

import com.palantir.javapoet.*;
import edu.kit.iti.formal.astgen.gen.HierarchyGenerator;
import edu.kit.iti.formal.astgen.model.Hierarchy;

/**
 * @author Alexander Weigl
 * @version 1 (10.09.17)
 */
public class VisitorGenerator implements HierarchyGenerator {

    @Override
    public List<JavaFile> modify(Path sourceFolder, Hierarchy hierarchy) {
        return List.of(
            extracted(hierarchy, 0),
            extracted(hierarchy, 1));
    }

    private static JavaFile extracted(Hierarchy hierarchy, int arg) {
        var typeR = TypeVariableName.get("R");
        var typeT =
            IntStream.range(0, arg).mapToObj(it -> TypeVariableName.get("T" + it)).toList();

        var methods = hierarchy.nodes().stream().map(node -> {
            var m = MethodSpec.methodBuilder("visit");
            m.addParameter(ClassName.bestGuess(node.name()), "node");
            for (int i = 0; i < arg; i++) {
                m.addParameter(typeT.get(i), "arg" + i);
            }
            return m.build();
        }).toList();

        var pckg = hierarchy.mainPackage();
        var ts = TypeSpec.interfaceBuilder(ClassName.get(pckg, "Visitor" + arg))
                .addMethods(methods)
                .build();
        return JavaFile.builder(pckg, ts).build();
    }
}
