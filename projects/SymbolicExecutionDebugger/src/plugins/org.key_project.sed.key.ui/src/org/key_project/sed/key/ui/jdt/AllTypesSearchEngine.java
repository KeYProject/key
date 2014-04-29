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
 * Searches all available Java types ({@link IType}).
 * </p>
 * <p>
 * Usage example:
 * <pre><code>
 * IJavaProject javaProject = ...;
 * IJavaSearchScope searchScope = SearchEngine.createJavaSearchScope(new IJavaElement[] {javaProject}, IJavaSearchScope.SOURCES);
 * AllTypesSearchEngine engine = new AllTypesSearchEngine();
 * engine.setIncludeAnnotations(true);
 * engine.setIncludeInnerAndAnonymousTypes(true);
 * IType[] types = engine.searchTypes(new NullProgressMonitor(), searchScope);
 * </code></pre>
 * </p>
 * <p>
 * The implementation is oriented at {@link MainMethodSearchEngine}.
 * </p>
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class AllTypesSearchEngine {
    /**
     * Include inner and anonymous types in the search result?
     */
    private boolean includeInnerAndAnonymousTypes = false;
    
    /**
     * Include annotations in the search result?
     */
    private boolean includeAnnotations = false;

    /**
     * Implementation of {@link SearchRequestor} to collect found
     * {@link IType}s in a search.
     * @author Martin Hentschel
     */
    private class TypeCollector extends SearchRequestor {
        /**
         * Contains all found {@link IType}s.
         */
        private List<IType> result = new LinkedList<IType>();

        /**
         * Returns the found {@link IType}s.
         * @return The found {@link IType}s.
         */
        public List<IType> getResult() {
            return result;
        }

        /**
         * Checks if the found element is a valid result and adds it 
         * to {@link #getResult()}.
         */
        @Override
        public void acceptSearchMatch(SearchMatch match) throws CoreException {
            Object enclosingElement = match.getElement();
            if (enclosingElement instanceof IType) {
                IType type = (IType)enclosingElement;
                if ((isIncludeInnerAndAnonymousTypes() || (!type.isMember() && !type.isAnonymous())) &&
                    (isIncludeAnnotations() || !type.isAnnotation())) {
                    result.add(type);
                }
            }
        }
    }

    /**
     * Searches all types.
     * @param pm The {@link IProgressMonitor} to use.
     * @param scope The {@link IJavaSearchScope} to search in.
     * @return The found {@link IType}s.
     */
    public IType[] searchTypes(IProgressMonitor pm, IJavaSearchScope scope) {
        pm.beginTask("Searching for types...", 100);
        int searchTicks = 100;
        SearchPattern pattern = SearchPattern.createPattern("*",
                                                            IJavaSearchConstants.TYPE,
                                                            IJavaSearchConstants.ALL_OCCURRENCES, 
                                                            SearchPattern.R_EXACT_MATCH | SearchPattern.R_CASE_SENSITIVE);
        SearchParticipant[] participants = new SearchParticipant[] {SearchEngine.getDefaultSearchParticipant()};
        TypeCollector collector = new TypeCollector();
        IProgressMonitor searchMonitor = new SubProgressMonitor(pm, searchTicks);
        try {
            new SearchEngine().search(pattern, participants, scope, collector, searchMonitor);
        }
        catch (CoreException ce) {
            LogUtil.getLogger().logError(ce);
        }
        List<IType> result = collector.getResult();
        return result.toArray(new IType[result.size()]);
    }
    
    /**
     * Searches all types.
     * @param context The {@link IRunnableContext} to search in.
     * @param scope The {@link IJavaSearchScope} to search in.
     * @return The found {@link IType}s.
     * @throws InvocationTargetException Occurred Exception.
     * @throws InterruptedException Occurred Exception.
     */
    public IType[] searchTypes(IRunnableContext context, 
                               final IJavaSearchScope scope) throws InvocationTargetException, InterruptedException {
        final IType[][] res = new IType[1][];
        IRunnableWithProgress runnable = new IRunnableWithProgress() {
            public void run(IProgressMonitor pm) throws InvocationTargetException {
                res[0] = searchTypes(pm, scope);
            }
        };
        context.run(true, true, runnable);
        return res[0];
    }

    /**
     * Checks if inner and anonymous types are included in the search result?
     * @return {@code true} included, {@code false} not included.
     */
    public boolean isIncludeInnerAndAnonymousTypes() {
        return includeInnerAndAnonymousTypes;
    }

    /**
     * Defines if inner and anonymous types are included in the search result?
     * @param includeInnerAndAnonymousTypes {@code true} included, {@code false} not included.
     */
    public void setIncludeInnerAndAnonymousTypes(boolean includeInnerAndAnonymousTypes) {
        this.includeInnerAndAnonymousTypes = includeInnerAndAnonymousTypes;
    }
    
    /**
     * Checks if annotations are included in the search result.
     * @return {@code true} included, {@code false} not included.
     */
    public boolean isIncludeAnnotations() {
        return includeAnnotations;
    }

    /**
     * Defines if annotations are included in the search result.
     * @param includeAnnotations {@code true} included, {@code false} not included.
     */
    public void setIncludeAnnotations(boolean includeAnnotations) {
        this.includeAnnotations = includeAnnotations;
    }
}