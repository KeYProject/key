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

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.viewers.ILabelProvider;
import org.key_project.util.eclipse.swt.viewer.AbstractSimpleHTMLLabelProvider;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.Contract;

/**
 * An {@link ILabelProvider} that can be used to show {@link Contract}s.
 * @author Martin Hentschel
 */
public class ContractLabelProvider extends AbstractSimpleHTMLLabelProvider {
    /**
     * The {@link Services} to use.
     */
    private final Services services;
    
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
    protected String getHtml(Object element) {
       String html = null;
       String displayName = null;
       // Convert contract to HTML 
       if (element instanceof Contract) {
          Contract contract = (Contract) element;
          html = contract.getHTMLText(services);
          displayName = contract.getDisplayName();
       }
       else if (element instanceof BlockContract) {
          BlockContract bc = (BlockContract) element;
          html = bc.getHtmlText(services);
          displayName = bc.getDisplayName();
       }
       // Insert contract name into HTML
       if (displayName != null) {
          if (html != null) {
             int start = html.indexOf("<html>");
             if (start >= 0) {
                 // A real border with tile via <fieldset><legend>Title</legend>Content</fieldset> is not supported by Swing
                 int end = html.indexOf("</html>", start + "<html>".length());
                 String text = end >= 0 ?
                               html.substring(start + "<html>".length(), end) :
                               html.substring(start + "<html>".length());
                 html = "<html><body><h2>" + 
                        displayName + "</h2><br>" + 
                        text +
                        "</body></html>";
             }
          }
          else {
             html = "<html><body><h2>" + displayName + "</h2></body></html>";
          }
       }
       return html;
    }
}