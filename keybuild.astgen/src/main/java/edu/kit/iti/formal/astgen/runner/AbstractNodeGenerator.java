/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package edu.kit.iti.formal.astgen.runner;

import edu.kit.iti.formal.astgen.gen.NodeGenerator;
import edu.kit.iti.formal.astgen.model.Hierarchy;

/**
 * @author Alexander Weigl
 * @version 1 (10.09.17)
 */
public abstract class AbstractNodeGenerator implements NodeGenerator {
    private Hierarchy hierarchy;

    public Hierarchy getHierarchy() {
        return hierarchy;
    }

    @Override
    public void setHierarchy(Hierarchy hierarchy) {
        this.hierarchy = hierarchy;
    }
}
