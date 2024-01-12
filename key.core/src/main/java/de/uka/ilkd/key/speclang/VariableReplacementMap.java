/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/**
 * A replacement map for variables.
 *
 * @author lanzinger
 */
public class VariableReplacementMap extends ReplacementMap<ProgramVariable> {

    /**
     * constructs a replacement map with the given term factory
     *
     * @param tf a term factory
     */
    public VariableReplacementMap(TermFactory tf) {
        super(tf);
    }

    @Override
    protected ProgramVariable convert(ProgramVariable variable, TermServices services) {
        return variable;
    }

}
