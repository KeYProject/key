/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.declaration;

import recoder.java.Declaration;
import recoder.java.ProgramElement;

/**
 * @author gutzmann
 */
public interface DeclarationSpecifier extends ProgramElement {
    void setParent(Declaration parent);

    Declaration getParentDeclaration();
}
