package org.key_project.jmlediting.core.resolver.typecomputer;

import org.eclipse.jdt.core.dom.ITypeBinding;
import org.key_project.jmlediting.core.dom.IASTNode;

public interface ITypeComputer {

   /**
    * Computes the Type of the given {@link IASTNode} recursively.
    * 
    * @param node the {@link IASTNode}, that is tested
    * @return the {@link ITypeBinding} of the resulting type
    * @throws {@link TypeComputerException} if there is a type mismatch or something could not
    *         be resolved
    */
   public ITypeBinding computeType(IASTNode node) throws TypeComputerException;
}
