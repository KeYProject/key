/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.visitor;

import de.uka.ilkd.key.java.ProgramElement;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * Walks through a java AST in depth-left-fist-order. You can set the type of nodes you want to
 * collect and then {@link #start()} the walker. The found nodes of the given type are returned as a
 * list of {@link ProgramElement}.
 */
public class JavaASTCollector extends JavaASTWalker {

    /** the type of nodes to be collected */
    private final Class<?> type;
    /** the list of found elements */
    private ImmutableList<ProgramElement> resultList = ImmutableSLList.nil();

    /**
     * create the JavaASTWalker
     *
     * @param root the ProgramElement where to begin
     * @param type the Class representing the type of nodes that have to be collected
     */
    public JavaASTCollector(ProgramElement root, Class<?> type) {
        super(root);
        this.type = type;
    }

    /**
     * the action that is performed just before leaving the node the last time
     */
    protected void doAction(ProgramElement node) {
        if (type.isInstance(node)) {
            resultList = resultList.prepend(node);
        }
    }

    /**
     * returns the found nodes of the specified type
     *
     * @return the found nodes of the specified type as list
     */
    public ImmutableList<ProgramElement> getNodes() {
        return resultList;
    }

}
