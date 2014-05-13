/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.sed.key.ui.jdt;

import java.lang.reflect.InvocationTargetException;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.SubProgressMonitor;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.search.IJavaSearchConstants;
import org.eclipse.jdt.core.search.IJavaSearchScope;
import org.eclipse.jdt.core.search.SearchEngine;
import org.eclipse.jdt.core.search.SearchMatch;
import org.eclipse.jdt.core.search.SearchParticipant;
import org.eclipse.jdt.core.search.SearchPattern;
import org.eclipse.jdt.core.search.SearchRequestor;
import org.eclipse.jdt.internal.debug.ui.launcher.MainMethodSearchEngine;
import org.eclipse.jface.operation.IRunnableContext;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.key_project.sed.key.ui.util.LogUtil;

/**
 * <p>
 * Searches all available Java methods and constructors ({@link IMethod}).
 * </p>
 * <p>
 * Usage example:
 * <pre><code>
 * IJavaProject javaProject = ...;
 * IJavaSearchScope searchScope = SearchEngine.createJavaSearchScope(new IJavaElement[] {javaProject}, IJavaSearchScope.SOURCES);
 * AllOperationsSearchEngine engine = new AllOperationsSearchEngine();
 * engine.setIncludeOperationsOfAnnotations(true);
 * engine.setIncludeOperationsOfInnerAndAnonymousTypes(true);
 * IMethod[] methods = engine.searchOperations(new NullProgressMonitor(), searchScope);
 * </code></pre>
 * </p>
 * <p>
 * The implementation is oriented at {@link MainMethodSearchEngine}.
 * </p>
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class AllOperationsSearchEngine {
    /**
     * Include operations of inner and anonymous types in the search result?
     */
    private boolean includeOperationsOfInnerAndAnonymousTypes = false;

    /**
     * Include operations of annotations?
     */
    private boolean includeOperationsOfAnnotations = false;

    /**
     * Implementation of {@link SearchRequestor} to collect found
     * {@link IMethod}s in a search.
     * @author Martin Hentschel
     */
    private class MethodCollector extends SearchRequestor {
        /**
         * Contains all found {@link IMethod}s.
         */
        private List<IMethod> result = new LinkedList<IMethod>();

        /**
         * Returns the found {@link IMethod}s.
         * @return The found {@link IMethod}s.
         */
        public List<IMethod> getResult() {
            return result;
        }

        /**
         * Checks if the found element is a valid result and adds it 
         * to {@link #getResult()}.
         */
        @Override
        public void acceptSearchMatch(SearchMatch match) throws CoreException {
            Object enclosingElement = match.getElement();
            if (enclosingElement instanceof IMethod) {
                IMethod method = (IMethod)enclosingElement;
                IType type = (IType)method.getParent();
                if ((isIncludeOperationsOfInnerAndAnonymousTypes() || (!type.isMember() && !type.isAnonymous())) &&
                    (isIncludeOperationsOfAnnotations() || !type.isAnnotation())) {
                    result.add(method);
                }
            }
        }
    }

    /**
     * Searches all methods and constructors.
     * @param pm The {@link IProgressMonitor} to use.
     * @param scope The {@link IJavaSearchScope} to search in.
     * @return The found {@link IMethod}s.
     */
    public IMethod[] searchOperations(IProgressMonitor pm, IJavaSearchScope scope) {
        pm.beginTask("Searching for methods...", 100);
        int searchTicks = 100;
        SearchPattern constructorPattern = SearchPattern.createPattern("*", 
                                                                       IJavaSearchConstants.CONSTRUCTOR, 
                                                                       IJavaSearchConstants.DECLARATIONS, 
                                                                       SearchPattern.R_EXACT_MATCH | SearchPattern.R_CASE_SENSITIVE);
        SearchPattern methodPattern = SearchPattern.createPattern("*",
                                                                  IJavaSearchConstants.METHOD, 
                                                                  IJavaSearchConstants.DECLARATIONS, 
                                                                  SearchPattern.R_EXACT_MATCH | SearchPattern.R_CASE_SENSITIVE);
        SearchPattern pattern = SearchPattern.createOrPattern(constructorPattern, methodPattern);
        SearchParticipant[] participants = new SearchParticipant[] {SearchEngine.getDefaultSearchParticipant()};
        MethodCollector collector = new MethodCollector();
        IProgressMonitor searchMonitor = new SubProgressMonitor(pm, searchTicks);
        try {
            new SearchEngine().search(pattern, participants, scope, collector, searchMonitor);
        }
        catch (CoreException ce) {
            LogUtil.getLogger().logError(ce);
        }
        List<IMethod> result = collector.getResult();
        return result.toArray(new IMethod[result.size()]);
    }
    
    /**
     * Searches all methods and constructors.
     * @param context The {@link IRunnableContext} to search in.
     * @param scope The {@link IJavaSearchScope} to search in.
     * @return The found {@link IMethod}s.
     * @throws InvocationTargetException Occurred Exception.
     * @throws InterruptedException Occurred Exception.
     */
    public IMethod[] searchOperations(IRunnableContext context, 
                                   final IJavaSearchScope scope) throws InvocationTargetException, InterruptedException {
        final IMethod[][] res = new IMethod[1][];
        IRunnableWithProgress runnable = new IRunnableWithProgress() {
            public void run(IProgressMonitor pm) throws InvocationTargetException {
                res[0] = searchOperations(pm, scope);
            }
        };
        context.run(true, true, runnable);
        return res[0];
    }

    /**
     * Checks if methods and constructors of if inner and anonymous types are included in the search result?
     * @return {@code true} included, {@code false} not included.
     */
    public boolean isIncludeOperationsOfInnerAndAnonymousTypes() {
        return includeOperationsOfInnerAndAnonymousTypes;
    }

    /**
     * Defines if methods and constructors of inner and anonymous types are included in the search result?
     * @param includeOperationsOfInnerAndAnonymousTypes {@code true} included, {@code false} not included.
     */
    public void setIncludeOperationsOfInnerAndAnonymousTypes(boolean includeOperationsOfInnerAndAnonymousTypes) {
        this.includeOperationsOfInnerAndAnonymousTypes = includeOperationsOfInnerAndAnonymousTypes;
    }

    /**
     * Checks if methods of annotations are included in the search result.
     * @return {@code true} included, {@code false} not included.
     */
    public boolean isIncludeOperationsOfAnnotations() {
        return includeOperationsOfAnnotations;
    }

    /**
     * Defines if methods of annotations are included in the search result.
     * @param includeOperationsOfAnnotations {@code true} included, {@code false} not included.
     */
    public void setIncludeOperationsOfAnnotations(boolean includeOperationsOfAnnotations) {
        this.includeOperationsOfAnnotations = includeOperationsOfAnnotations;
    }
}