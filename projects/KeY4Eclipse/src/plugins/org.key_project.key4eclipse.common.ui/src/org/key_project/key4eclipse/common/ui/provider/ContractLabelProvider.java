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

package org.key_project.key4eclipse.common.ui.provider;

import java.awt.image.BufferedImage;
import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.ImageData;
import org.eclipse.swt.widgets.Display;
import org.key_project.util.eclipse.swt.ImageUtil;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.speclang.Contract;

/**
 * An {@link ILabelProvider} that can be used to show {@link Contract}s.
 * @author Martin Hentschel
 */
public class ContractLabelProvider extends LabelProvider {
    /**
     * The {@link Services} to use.
     */
    private Services services;
    
    /**
     * Contains rendered HTML images.
     */
    private Map<Object, Image> cache = new HashMap<Object, Image>();
    
    /**
     * Constructor.
     * @param services The {@link Services} to use.
     */
    public ContractLabelProvider(Services services) {
        Assert.isNotNull(services);
        this.services = services;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Image getImage(Object element) {
        if (element instanceof Contract) {
            Image image = cache.get(element);
            if (image == null) {
                // Convert contract to HTML 
                Contract contract = (Contract)element;
                String html = contract.getHTMLText(services);
                // Insert contract name into HTML
                int index = html.indexOf("<html>");
                if (index >= 0) {
                    // A real border with tile via <fieldset><legend>Title</legend>Content</fieldset> is not supported by Swing 
                    html = html.substring(0, index) + 
                           "<html><h2>" + contract.getName() + "</h2>" + 
                           html.substring(index + "<html>".length());
                }
                // Create image
                BufferedImage javaImage = ImageUtil.renderHTML(html, true, true);
                ImageData data = ImageUtil.convertToImageData(javaImage);
                image = new Image(Display.getDefault(), data);
                cache.put(element, image);
            }
            return image;
        }
        else {
            return super.getImage(element);
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getText(Object element) {
        if (element instanceof Contract) {
            return null; // Don't show text because an Image is shown, with text the columns are to big
        }
        else {
            return super.getText(element);
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void dispose() {
        for (Image image : cache.values()) {
            image.dispose();
        }
        cache.clear();
        super.dispose();
    }
}