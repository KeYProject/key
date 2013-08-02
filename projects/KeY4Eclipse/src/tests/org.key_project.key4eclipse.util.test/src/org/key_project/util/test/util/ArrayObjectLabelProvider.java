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

package org.key_project.util.test.util;

import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;
import org.key_project.util.java.ObjectUtil;

/**
 * Implementation of {@link ITableLabelProvider} for {@link ArrayObject}s.
 * @author Martin Hentschel
 */
public class ArrayObjectLabelProvider extends LabelProvider implements ITableLabelProvider {
    /**
     * {@inheritDoc}
     */
    @Override
    public Image getColumnImage(Object element, int columnIndex) {
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getColumnText(Object element, int columnIndex) {
        if (element instanceof ArrayObject) {
            return ObjectUtil.toString(((ArrayObject)element).getValue(columnIndex));
        }
        else {
            return null;
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getText(Object element) {
        return getColumnText(element, 0);
    }
}