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

package org.key_project.sed.ui.visualization.object_diagram.property;

import org.eclipse.jface.viewers.IFilter;

/**
 * {@link IFilter} implementation used to define if a {@link AssociationPropertySection}
 * is available or not.
 * @author Martin Hentschel
 */
public class AssociationTreeFilter extends AbstractObjectDiagramTreeFilter {
   /**
    * {@inheritDoc}
    */
   @Override
   protected AbstractObjectDiagramPropertySection<?> createPropertySection() {
      return new AssociationPropertySection();
   }
}