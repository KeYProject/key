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

package org.key_project.sed.ui.visualization.object_diagram.provider;

import org.key_project.sed.ui.visualization.model.od.ODAssociation;
import org.key_project.sed.ui.visualization.model.od.ODObject;
import org.key_project.sed.ui.visualization.model.od.ODState;
import org.key_project.sed.ui.visualization.model.od.ODValue;

/**
 * <p>
 * This interface provides predefined image constants which can be used by the
 * features for image graphics algorithm.
 * </p>
 * <p>
 * Images itself are provided via {@link ObjectDiagramImageProvider} which
 * is instantiated and managed by Graphiti's extension points.
 * </p>
 * @author Martin Hentschel
 * @see ObjectDiagramImageProvider
 */
public interface IObjectDiagramImageConstants {
   /**
    * The constant prefix of all image keys.
    */
   public static final String PREFIX = "org.key_project.sed.ui.visualization.";
   
   /**
    * Key of the image for {@link ODObject}s.
    */
   public static final String IMG_OBJECT = PREFIX + "object";

   /**
    * Key of the image for {@link ODAssociation}s.
    */
   public static final String IMG_ASSOCIATION = PREFIX + "association";

   /**
    * Key of the image for {@link ODValue}s.
    */
   public static final String IMG_VALUE = PREFIX + "value";

   /**
    * Key of the image for {@link ODState}s.
    */
   public static final String IMG_STATE = PREFIX + "state";
}