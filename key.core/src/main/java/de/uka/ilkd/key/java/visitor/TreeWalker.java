/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.visitor;

import de.uka.ilkd.key.java.SourceElement;

public interface TreeWalker {
    SourceElement getRoot();

    SourceElement getCurrentNode();

    SourceElement firstChild();

    SourceElement lastChild();

    SourceElement nextNode();

    SourceElement previousNode();

    SourceElement nextSibling();

    SourceElement previousSibling();

    SourceElement parentNode(); // leave out or by using a stack storing pair of parent and index
                                // for sibling
}
