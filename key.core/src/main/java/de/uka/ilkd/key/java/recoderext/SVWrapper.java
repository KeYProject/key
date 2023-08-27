/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import de.uka.ilkd.key.logic.op.SchemaVariable;

public interface SVWrapper {

    /**
     * sets the schema variable of sort statement
     *
     * @param sv the SchemaVariable to wrap
     */
    void setSV(SchemaVariable sv);

    /**
     * returns a String name of this meta construct.
     */
    SchemaVariable getSV();


}
