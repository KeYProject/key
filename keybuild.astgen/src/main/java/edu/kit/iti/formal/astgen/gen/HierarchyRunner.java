/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package edu.kit.iti.formal.astgen.gen;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import com.palantir.javapoet.JavaFile;

/**
 * @author Alexander Weigl
 * @version 1 (10.09.17)
 */
public class HierarchyRunner extends AbstractRunner {
    private List<HierarchyGenerator> generators = new ArrayList<>();

    public HierarchyRunner() {}

    @Override
    public void process() {
        for (HierarchyGenerator generator : generators) {
            var files = generator.modify(sourceDirectory, hierarchy);
            for (JavaFile file : files) {
                try {
                    file.writeToPath(sourceDirectory);
                } catch (IOException e) {
                    throw new RuntimeException(e);
                }
            }
        }
    }

    public List<HierarchyGenerator> getGenerators() {
        return generators;
    }

    public void setGenerators(List<HierarchyGenerator> generators) {
        this.generators = generators;
    }
}
