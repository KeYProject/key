package org.key_project.jmlediting.core.resolver;

import org.eclipse.jdt.core.ICompilationUnit;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.resolver.ResolveResult;

public interface IResolver {

    /**
     * Resolves an identifier inside of a JML comment. 
     * It will find the JavaElement or JML Element the {@link IASTNode} is referring to. 
     * If it can not find the JavaElement or JML element, it will return null.
     * 
     * @param cu 
     *      is the {@link ICompilationUnit} of the file, the {@link IASTNode} to be resolved is in
     * @param toResolve
     *      is the {@link IASTNode} of the identifier, that will be resolved. Possible children nodes are ignored.
     * @return a {@link ResolveResult} with the resolve information for that {@link IASTNode}, if it was able to be resolved.
     *         Otherwise it will return null.
     */
    ResolveResult resolve(final ICompilationUnit cu, final IASTNode toResolve) throws ResolverException;
    
    /** This method should be called after resolve(...).
     *  <br>It uses the information built by resolve(...) and resolves an identifier at a time.
     *  <br><br><b>Example:</b> {@code SomeClass.memberAccess.memberAccess2()}
     *  <br>When resolve(...) is called {@code SomeClass} is being resolved.
     *  <br>Then on the first next() call {@code memberAccess} is being resolved.
     *  <br>And on the second next() call {@code memberAccess2()} is being resolved.
     * 
     * @return the {@link ResolveResult} gotten from the current step
     * <br> or null if it could not be resolved or there are no more steps to take
     */
    ResolveResult next() throws ResolverException;
    
    /** This method returns true, if there should be another result.
     * 
     * @return true, if there is still work to do. False, otherwise.
     */
    boolean hasNext();
}
