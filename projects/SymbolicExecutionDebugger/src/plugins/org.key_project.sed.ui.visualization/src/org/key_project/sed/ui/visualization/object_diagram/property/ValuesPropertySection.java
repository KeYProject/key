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

import java.util.LinkedList;
import java.util.List;

import org.eclipse.emf.ecore.EObject;
import org.eclipse.graphiti.ui.services.GraphitiUi;
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
import org.key_project.sed.ui.visualization.model.od.ODAssociation;
import org.key_project.sed.ui.visualization.model.od.ODValue;
import org.key_project.sed.ui.visualization.object_diagram.provider.IObjectDiagramImageConstants;
import org.key_project.util.eclipse.swt.SWTUtil;

/**
 * {@link ISection} implementation to show values and association of {@link AbstractODValueContainer}s.
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
            else if (element instanceof ODAssociation) {
               switch (columnIndex) {
                  case 0 : return ((ODAssociation)element).getName();
                  case 1 : return ((ODAssociation)element).getTarget().getName();
                  case 2 : return ((ODAssociation)element).getTarget().getType();
                  default : return null;
               }
            }
            else {
               return null;
            }
         }
         
         @Override
         public Image getColumnImage(Object element, int columnIndex) {
            if (columnIndex == 0) {
               if (element instanceof ODValue) {
                  return GraphitiUi.getImageService().getImageForId(IObjectDiagramImageConstants.IMG_VALUE);
               }
               else if (element instanceof ODAssociation) {
                  return GraphitiUi.getImageService().getImageForId(IObjectDiagramImageConstants.IMG_ASSOCIATION);
               }
               else {
                  return null;
               }
            }
            else {
               return null;
            }
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
      List<EObject> input = new LinkedList<EObject>();
      input.addAll(getBusinessObject().getValues());
      input.addAll(getBusinessObject().getAssociations());
      viewer.setInput(input);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean isBusinessObjectSupported(Object bo) {
      return bo instanceof AbstractODValueContainer;
   }
}