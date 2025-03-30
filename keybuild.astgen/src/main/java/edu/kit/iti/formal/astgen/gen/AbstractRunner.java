/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package edu.kit.iti.formal.astgen.gen;

import java.nio.file.Path;

import edu.kit.iti.formal.astgen.model.Hierarchy;

/**
 * @author Alexander Weigl
 * @version 1 (10.09.17)
 */
public abstract class AbstractRunner implements Runnable {
    protected Hierarchy hierarchy;

    protected Path sourceDirectory;

    @Override
    public void run() {
        try {
            process();
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    protected abstract void process() throws Exception;

    public Hierarchy getHierarchy() {
        return hierarchy;
    }

    public void setHierarchy(Hierarchy hierarchy) {
        this.hierarchy = hierarchy;
    }

    public Path getSourceDirectory() {
        return sourceDirectory;
    }

    public void setSourceDirectory(Path sourceDirectory) {
        this.sourceDirectory = sourceDirectory;
    }
}
