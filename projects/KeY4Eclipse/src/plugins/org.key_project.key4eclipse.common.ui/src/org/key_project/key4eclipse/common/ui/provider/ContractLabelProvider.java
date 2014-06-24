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
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.ImageData;
import org.eclipse.swt.widgets.Display;
import org.key_project.util.eclipse.swt.ImageUtil;
import org.key_project.util.eclipse.swt.viewer.AbstractFullImageLabelProvider;
import org.key_project.util.java.ColorUtil;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.util.Pair;

/**
 * An {@link ILabelProvider} that can be used to show {@link Contract}s.
 * @author Martin Hentschel
 */
public class ContractLabelProvider extends AbstractFullImageLabelProvider {
    /**
     * The {@link Services} to use.
     */
    private final Services services;
    
    /**
     * Contains rendered HTML images.
     */
    private final Map<Pair<Object, Color>, Image> cache = new HashMap<Pair<Object, Color>, Image>();
    
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
    public Image getImage(Object element, int index, Color background, Color foreground) {
        if (element instanceof Contract) {
           Pair<Object, Color> pair = new Pair<Object, Color>(element, background);
           Image image = cache.get(pair);
           if (image == null) {
               // Convert contract to HTML 
               Contract contract = (Contract)element;
               String html = contract.getHTMLText(services);
               // Insert contract name into HTML
               int start = html.indexOf("<html>");
               if (start >= 0) {
                   // A real border with tile via <fieldset><legend>Title</legend>Content</fieldset> is not supported by Swing
                   int end = html.indexOf("</html>", start + "<html>".length());
                   String text = end >= 0 ?
                                 html.substring(start + "<html>".length(), end) :
                                 html.substring(start + "<html>".length());
                   String foregroundHex = ColorUtil.toHexRGBString(foreground);
                   html = "<html><body bgcolor=\"#" + ColorUtil.toHexRGBString(background) + "\"><h2 style=\"color: #" + foregroundHex + ";\">" + 
                          contract.getDisplayName() + "</h2>" + 
                          "<font color=\"#" + foregroundHex + "\">" + text +
                          "</font></body></html>";
               }
               // Create image
               BufferedImage javaImage = ImageUtil.renderHTML(html, true, true);
               ImageData data = ImageUtil.convertToImageData(javaImage);
               image = new Image(Display.getDefault(), data);
               cache.put(pair, image);
           }
           return image;
        }
        else {
            return null;
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