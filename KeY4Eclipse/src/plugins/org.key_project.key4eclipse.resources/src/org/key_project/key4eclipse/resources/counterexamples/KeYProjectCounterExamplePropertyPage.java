package org.key_project.key4eclipse.resources.counterexamples;

import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.TabFolder;
import org.eclipse.swt.widgets.TabItem;
import org.eclipse.ui.dialogs.PropertyPage;
import org.key_project.util.java.ArrayUtil;

public class KeYProjectCounterExamplePropertyPage extends PropertyPage {

    private KeYProjectCounterExampleModel model;
    
    public KeYProjectCounterExamplePropertyPage(KeYProjectCounterExampleModel model) {
        this.model = model;
        noDefaultAndApplyButton();
    }
    
    @Override
    protected Control createContents(Composite parent) {
        TabFolder tabFolder = new TabFolder(parent, SWT.NONE);
        TreeViewer viewer = new TreeViewer(tabFolder, SWT.MULTI);
        viewer.setContentProvider(new KeYProjectCounterExampleModelContentProvider());
        viewer.setLabelProvider(new KeYProjectCounterExampleLabelProvider());
        viewer.setInput(model);
        TabItem item = new TabItem(tabFolder, SWT.NONE);
        item.setText("Counter Example");
        item.setControl(viewer.getControl());
        tabFolder.setSelection(item);
        return tabFolder;
    }

    
    protected class KeYProjectCounterExampleModelContentProvider implements ITreeContentProvider {

        @Override
        public void dispose() {
        }

        @Override
        public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
        }

        @Override
        public Object[] getElements(Object inputElement) {
            return getChildren(inputElement);
        }

        @Override
        public Object[] getChildren(Object parentElement) {
            if(parentElement instanceof KeYProjectCounterExampleModel){
                return ((KeYProjectCounterExampleModel) parentElement).getTreeElements().toArray();
            }
            else if(parentElement instanceof TreeElement) {
                return ((TreeElement) parentElement).getChildren().toArray();
            }
            else return new Object[0];
        }

        @Override
        public Object getParent(Object element) {
            return null;
        }

        @Override
        public boolean hasChildren(Object element) {
            return !ArrayUtil.isEmpty(getChildren(element));
        }
    }
    
    protected class KeYProjectCounterExampleLabelProvider extends LabelProvider {

        @Override
        public String getText(Object element) {
           if (element instanceof TreeElement) {
              return ((TreeElement) element).toString();
           }
           else {
              return super.getText(element);
           }
        }
     }
}
