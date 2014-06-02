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

package org.key_project.sed.ui.visualization.object_diagram.provider;

import org.eclipse.graphiti.ui.platform.AbstractImageProvider;
import org.eclipse.graphiti.ui.platform.IImageProvider;

/**
 * <p>
 * {@link IImageProvider} specific implementation for object diagrams.
 * </p>
 * <p>
 * The constants of provided images are specified via interface {@link IObjectDiagramImageConstants}.
 * </p>
 * <p>
 * This class is instantiated an managed by Graphiti's extension points.
 * </p>
 * @author Martin Hentschel
 * @see IObjectDiagramImageConstants
 */
public class ObjectDiagramImageProvider extends AbstractImageProvider {
   /**
    * Path to the folder which contains the provided images.
    */
   private static final String ROOT_FOLDER_FOR_IMG = "icons/";

   /**
    * {@inheritDoc}
    */
   @Override
   protected void addAvailableImages() {
       addImageFilePath(IObjectDiagramImageConstants.IMG_OBJECT, ROOT_FOLDER_FOR_IMG + "object.gif");
       addImageFilePath(IObjectDiagramImageConstants.IMG_ASSOCIATION, ROOT_FOLDER_FOR_IMG + "association.gif");
       addImageFilePath(IObjectDiagramImageConstants.IMG_VALUE, ROOT_FOLDER_FOR_IMG + "value.gif");
       addImageFilePath(IObjectDiagramImageConstants.IMG_STATE, ROOT_FOLDER_FOR_IMG + "state.gif");
   }
}