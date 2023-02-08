/*
 * Created on 24.02.2005
 *
 * This file is part of the RECODER library and protected by the LGPL.
 */
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
