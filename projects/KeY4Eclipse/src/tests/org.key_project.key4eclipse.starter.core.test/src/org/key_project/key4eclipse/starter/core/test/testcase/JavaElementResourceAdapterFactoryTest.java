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

package org.key_project.key4eclipse.starter.core.test.testcase;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.Signature;
import org.junit.Test;
import org.key_project.key4eclipse.starter.core.adapter.JavaElementResourceAdapterFactory;
import org.key_project.key4eclipse.starter.core.test.Activator;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.test.testcase.AbstractSetupTestCase;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Tests for {@link JavaElementResourceAdapterFactory}.
 * @author Martin Hentschel
 */
public class JavaElementResourceAdapterFactoryTest extends AbstractSetupTestCase {
    /**
     * Tries to convert an {@link IMethod} into an {@link IResource}
     * via the adapter concept ({@link IMethod#getAdapter(Class)}).
     */
    @Test
    public void testAdaptingAnIMethodIntoAnIResource() throws CoreException, InterruptedException {
        // Create test project
        IJavaProject javaProject = TestUtilsUtil.createJavaProject("JavaElementResourceAdapterFactoryTest_testAdaptingAnIMethodIntoAnIResource");
        IFolder banking = javaProject.getProject().getFolder("src").getFolder("banking");
        if (!banking.exists()) {
            banking.create(true, true, null);
        }
        BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/banking", banking);
        IFile paycardFile = banking.getFile("PayCard.java");
        assertNotNull(paycardFile);
        assertTrue(paycardFile.exists());
        // Get method to test
        IMethod chargeMethod = TestUtilsUtil.getJdtMethod(javaProject, "banking.PayCard", "charge", Signature.C_INT + "");
        assertNotNull(chargeMethod);
        // Test direct conversion
        JavaElementResourceAdapterFactory factory = new JavaElementResourceAdapterFactory();
        IResource result = (IResource)factory.getAdapter(chargeMethod, IResource.class);
        assertNotNull(result);
        assertEquals(paycardFile, result);
        // Test adaptable concept
        IResource adaptedResource = (IResource)chargeMethod.getAdapter(IResource.class);
        assertNotNull(adaptedResource);
        assertEquals(paycardFile, adaptedResource);
    }
}