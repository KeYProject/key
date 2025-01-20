/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.reference;

import de.uka.ilkd.key.java.Reference;
import de.uka.ilkd.key.logic.op.IProgramMethod;

/**
 * extracted interface to allow schema variabes to stand for an execution context
 */
public interface IExecutionContext extends Reference {
    /**
     * returns the type reference to the next enclosing class
     *
     * @return the type reference to the next enclosing class
     */
    TypeReference getTypeReference();

    /**
     * returns the program method which is currently active
     *
     * @return the currently active method
     */
    IProgramMethod getMethodContext();

    /**
     * returns the runtime instance object
     *
     * @return the runtime instance object
     */
    ReferencePrefix getRuntimeInstance();
}
