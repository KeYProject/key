package org.key_project.jmlediting.core.resolver;

import org.eclipse.jdt.core.ICompilationUnit;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.resolver.ResolveResult;

/**
 * The IResolver Interface, that specifies three public methods. <br>
 * "{@code resolve}({@link ICompilationUnit}, {@link IASTNode}) -> {@link ResolveResult}" that
 * will resolve the {@link IASTNode} given and find the corresponding JavaElement or JML
 * declaration and <br>
 * "{@code next()} -> {@link ResolveResult}" that will resolve any member access that is
 * appended to the original identifier. <br>
 * "{@code hasNext()} -> boolean" that will return true, if the taskList is not empty and
 * there is still something to resolve with the next() method.
 * 
 * @author Christopher Beckmann
 */
public interface IResolver {

   /**
    * Resolves an identifier inside of a JML comment. It will find the JavaElement or JML
    * Element the {@link IASTNode} is referring to. If it can not find the JavaElement or JML
    * element, it will return null.
    * 
    * @param cu is the {@link ICompilationUnit} of the file, the {@link IASTNode} to be
    *           resolved is in
    * @param toResolve is the {@link IASTNode} of the identifier, that will be resolved.
    *           Possible children nodes are ignored.
    * @return a {@link ResolveResult} with the resolve information for that {@link IASTNode},
    *         if it was able to be resolved. Otherwise it will return null.
    * @throws ResolverException if the IASTNode is not build correctly, or the data can not be
    *            extracted.
    */
   ResolveResult resolve(final ICompilationUnit cu, final IASTNode toResolve)
            throws ResolverException;

   /**
    * This method should be called after resolve(...). <br>
    * It uses the information built by resolve(...) and resolves an identifier at a time. <br>
    * <br>
    * <b>Example:</b> {@code SomeClass.memberAccess.memberAccess2()} <br>
    * When resolve(...) is called {@code SomeClass} is being resolved. <br>
    * Then on the first next() call {@code memberAccess} is being resolved. <br>
    * And on the second next() call {@code memberAccess2()} is being resolved.
    * 
    * @return the {@link ResolveResult} gotten from the current step <br>
    *         or null if it could not be resolved or there are no more steps to take
    * @throws ResolverException if the context is not set correctly, although it should be.
    */
   ResolveResult next() throws ResolverException;

   /**
    * This method returns true, if there is more to be resolved.
    * 
    * @return true, if there is still work to do. false, otherwise.
    */
   boolean hasNext();
}
