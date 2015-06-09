package org.key_project.jmlediting.core.typechecker;

import org.eclipse.jdt.core.dom.ITypeBinding;
import org.key_project.jmlediting.core.dom.IASTNode;

public interface ITypeChecker {

    public ITypeBinding computeType(IASTNode node);
}
