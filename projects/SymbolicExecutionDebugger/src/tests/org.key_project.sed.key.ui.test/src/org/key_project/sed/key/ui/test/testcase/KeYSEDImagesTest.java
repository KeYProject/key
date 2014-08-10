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

package org.key_project.sed.key.ui.test.testcase;

import org.eclipse.swt.graphics.Image;
import org.junit.Test;
import org.key_project.sed.key.ui.util.KeYSEDImages;
import org.key_project.util.test.testcase.AbstractSetupTestCase;

/**
 * Contains tests for {@link KeYSEDImages}.
 * @author Martin Hentschel
 */
public class KeYSEDImagesTest extends AbstractSetupTestCase {
    /**
     * Tests {@link KeYSEDImages#getImage(String)}
     */
    @Test
    public void testGetImage() {
        // Test null
        assertNull(KeYSEDImages.getImage(null));
        // Test invalid
        assertNull(KeYSEDImages.getImage("INVALID"));
        // Test valid
        Image image = KeYSEDImages.getImage(KeYSEDImages.LAUNCH_MAIN_TAB_GROUP);
        assertNotNull(image);
        assertFalse(image.isDisposed());
        // Test valid image again
        Image imageAgain = KeYSEDImages.getImage(KeYSEDImages.LAUNCH_MAIN_TAB_GROUP);
        assertNotNull(imageAgain);
        assertFalse(imageAgain.isDisposed());
        assertSame(image, imageAgain);
    }
    
    /**
     * Tests {@link KeYSEDImages#disposeImages()}
     */
    @Test
    public void testDisposeImages() {
        // Test null image to make sure that they are not cached.
        assertNull(KeYSEDImages.getImage(null));
        // Test invalid image to make sure that they are not cached.
        assertNull(KeYSEDImages.getImage("INVALID"));
        // Get valid image
        Image image = KeYSEDImages.getImage(KeYSEDImages.LAUNCH_MAIN_TAB_GROUP);
        assertNotNull(image);
        assertFalse(image.isDisposed());
        // Dispose images
        KeYSEDImages.disposeImages();
        assertTrue(image.isDisposed());
        // Get valid image again
        Image imageAgain = KeYSEDImages.getImage(KeYSEDImages.LAUNCH_MAIN_TAB_GROUP);
        assertNotNull(imageAgain);
        assertFalse(imageAgain.isDisposed());
        assertNotSame(image, imageAgain);
    }
}