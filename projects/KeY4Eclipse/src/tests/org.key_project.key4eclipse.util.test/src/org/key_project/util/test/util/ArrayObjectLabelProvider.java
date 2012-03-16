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
