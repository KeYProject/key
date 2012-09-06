package org.key_project.sed.ui.visualization.object_diagram.property;

import org.eclipse.jface.layout.TableColumnLayout;
import org.eclipse.jface.viewers.ArrayContentProvider;
import org.eclipse.jface.viewers.ColumnWeightData;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.TableViewerColumn;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.views.properties.tabbed.ISection;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetPage;
import org.key_project.sed.ui.visualization.model.od.AbstractODValueContainer;
import org.key_project.sed.ui.visualization.model.od.ODValue;
import org.key_project.util.eclipse.swt.SWTUtil;

/**
 * {@link ISection} implementation to show properties of {@link AbstractODValueContainer}s.
 * @author Martin Hentschel
 */
public class ValuesPropertySection extends AbstractObjectDiagramPropertySection<AbstractODValueContainer> {
   /**
    * {@link TableViewer} used to show {@link AbstractODValueContainer#getValues()}.
    */
   private TableViewer viewer;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void createControls(Composite parent, TabbedPropertySheetPage tabbedPropertySheetPage) {
      super.createControls(parent, tabbedPropertySheetPage);
      
      Composite tableComposite = new Composite(parent, SWT.NONE);
      TableColumnLayout tableCompositeLayout = new TableColumnLayout();
      tableComposite.setLayout(tableCompositeLayout);
      
      viewer = new TableViewer(tableComposite, SWT.FULL_SELECTION | SWT.MULTI);
      viewer.getTable().setHeaderVisible(true);
      TableViewerColumn nameColumn = new TableViewerColumn(viewer, SWT.NONE);
      nameColumn.getColumn().setText("Name");
      nameColumn.getColumn().setMoveable(true);
      tableCompositeLayout.setColumnData(nameColumn.getColumn(), new ColumnWeightData(33));
      TableViewerColumn valueColumn = new TableViewerColumn(viewer, SWT.NONE);
      valueColumn.getColumn().setText("Value");
      valueColumn.getColumn().setMoveable(true);
      tableCompositeLayout.setColumnData(valueColumn.getColumn(), new ColumnWeightData(33));
      TableViewerColumn typeColumn = new TableViewerColumn(viewer, SWT.NONE);
      typeColumn.getColumn().setText("Type");
      typeColumn.getColumn().setMoveable(true);
      tableCompositeLayout.setColumnData(typeColumn.getColumn(), new ColumnWeightData(33));
      
      viewer.setContentProvider(ArrayContentProvider.getInstance());
      viewer.setLabelProvider(new ITableLabelProvider() {
         @Override
         public String getColumnText(Object element, int columnIndex) {
            if (element instanceof ODValue) {
               switch (columnIndex) {
                  case 0 : return ((ODValue)element).getName();
                  case 1 : return ((ODValue)element).getValue();
                  case 2 : return ((ODValue)element).getType();
                  default : return null;
               }
            }
            else {
               return null;
            }
         }
         
         @Override
         public Image getColumnImage(Object element, int columnIndex) {
            return null;
         }
         
         @Override
         public void removeListener(ILabelProviderListener listener) {
         }
         
         @Override
         public boolean isLabelProperty(Object element, String property) {
            return false;
         }
         
         @Override
         public void dispose() {
         }
         
         @Override
         public void addListener(ILabelProviderListener listener) {
         }
      });
      
      SWTUtil.makeTableColumnsSortable(viewer);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void refresh() {
      viewer.setInput(getBusinessObject().getValues());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean isBusinessObjectSupported(Object bo) {
      return bo instanceof AbstractODValueContainer;
   }
}