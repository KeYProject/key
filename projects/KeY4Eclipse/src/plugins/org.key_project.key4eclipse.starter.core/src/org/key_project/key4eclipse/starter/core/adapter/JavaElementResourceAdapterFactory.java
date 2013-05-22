/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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

package org.key_project.key4eclipse.starter.core.adapter;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IAdapterFactory;
import org.eclipse.jdt.core.IJavaElement;

/**
 * <p>
 * This implementation of {@link IAdapterFactory} is used to convert an
 * {@link IJavaElement} into the handled {@link IResource} instance.
 * </p>
 * <p>
 * For more details about the adapter concept in Eclipse have a look at:
 * <a href="http://help.eclipse.org/galileo/topic/org.eclipse.platform.doc.isv/reference/extension-points/org_eclipse_core_runtime_adapters.html">http://help.eclipse.org/galileo/topic/org.eclipse.platform.doc.isv/reference/extension-points/org_eclipse_core_runtime_adapters.html</a>
 * </p>
 * @author Martin Hentschel
 */
public class JavaElementResourceAdapterFactory implements IAdapterFactory {
    /**
     * {@inheritDoc}
     */
    @SuppressWarnings("rawtypes")
    @Override
    public Object getAdapter(Object adaptableObject, Class adapterType) {
        if (adaptableObject instanceof IJavaElement) {
            if (IResource.class.equals(adapterType)) {
                return ((IJavaElement)adaptableObject).getResource();
            }
            else {
                return null;
            }
        }
        else {
            return null;
        }
    }

    /**
     * {@inheritDoc}
     */
    @SuppressWarnings("rawtypes")
    @Override
    public Class[] getAdapterList() {
        return new Class[] {IResource.class};
    }
}