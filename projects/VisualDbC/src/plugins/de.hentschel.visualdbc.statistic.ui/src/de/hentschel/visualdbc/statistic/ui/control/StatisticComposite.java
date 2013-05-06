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

package de.hentschel.visualdbc.statistic.ui.control;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.Assert;
import org.eclipse.emf.common.notify.Adapter;
import org.eclipse.emf.common.notify.Notification;
import org.eclipse.emf.common.notify.impl.AdapterImpl;
import org.eclipse.emf.edit.provider.ComposedAdapterFactory;
import org.eclipse.emf.edit.provider.ReflectiveItemProviderAdapterFactory;
import org.eclipse.emf.edit.provider.resource.ResourceItemProviderAdapterFactory;
import org.eclipse.emf.edit.ui.provider.AdapterFactoryContentProvider;
import org.eclipse.emf.edit.ui.provider.AdapterFactoryLabelProvider;
import org.eclipse.jface.layout.TreeColumnLayout;
import org.eclipse.jface.viewers.ColumnWeightData;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.TreeViewerColumn;
import org.eclipse.ocl.util.ObjectUtil;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.TreeColumn;

import de.hentschel.visualdbc.dbcmodel.DbcModel;
import de.hentschel.visualdbc.dbcmodel.DbcProofObligation;
import de.hentschel.visualdbc.dbcmodel.DbcmodelPackage;
import de.hentschel.visualdbc.statistic.ui.emfAdapter.StatisticDbcmodelItemProviderAdapterFactory;
import de.hentschel.visualdbc.statistic.ui.util.StatisticColorDecorator;
import de.hentschel.visualdbc.statistic.ui.wizard.SelectProofObligationsWizard;

/**
 * Shows the static tree with the content provided by an {@link IStatisticProvider}.
 * @author Martin Hentschel
 */
public class StatisticComposite extends Composite {
   /**
    * The used {@link ComposedAdapterFactory}.
    */
   private ComposedAdapterFactory adapterFactory;
   
   /**
    * The shown model
    */
   private DbcModel model;
   
   /**
    * The shown {@link TreeViewer}.
    */
   private TreeViewer viewer;
   
   /**
    * The layout used to arrange in the columns in {@link #viewer}.
    */
   private TreeColumnLayout viewerLayout;
   
   /**
    * Contains all observed obligations.
    */
   private List<DbcProofObligation> observedObligations = new LinkedList<DbcProofObligation>();

   /**
    * The currently selected proof obligations.
    */
   private List<DbcProofObligation> selectedObligations = new LinkedList<DbcProofObligation>();
   
   /**
    * The {@link IStatisticProvider} that is used.
    */
   private IStatisticProvider statisticProvider;
   
   /**
    * Listens for changes on {@link #model} and {@link #observedObligations}.
    */
   private Adapter modelListener = new AdapterImpl() {
      @Override
      public void notifyChanged(Notification msg) {
         handleModelChanged(msg);
      }
   };
   
   /**
    * The used {@link StatisticColorDecorator}
    */
   private StatisticColorDecorator colorDecorator;
   
   /**
    * Constructor.
    * @param parent The parent {@link Composite}.
    * @param style The style to use.
    * @param statisticProvider The {@link IStatisticProvider} to use.
    */
   public StatisticComposite(Composite parent, 
                             int style,
                             IStatisticProvider statisticProvider) {
      super(parent, style);
      Assert.isNotNull(statisticProvider);
      this.statisticProvider = statisticProvider;
      // Set layout
      viewerLayout = new TreeColumnLayout();
      setLayout(viewerLayout);
      // Get model
      model = statisticProvider.getModel();
      if (model != null) {
         model.eAdapters().add(modelListener);
         selectedObligations = new LinkedList<DbcProofObligation>(model.getProofObligations());
      }
      // Create viewer
      updateViewer();
   }
   
   /**
    * Disposes the old viewer and creates a new one.
    */
   protected void updateViewer() {
      // Remove old viewer
      if (colorDecorator != null) {
         colorDecorator.dispose();
      }
      if (viewer != null) {
         viewer.getTree().dispose();
      }
      removeListenerFromProofObligations();
      if (adapterFactory != null) {
         adapterFactory.dispose();
      }
      // Create viewer
      viewer = new TreeViewer(this, SWT.BORDER | SWT.H_SCROLL | SWT.V_SCROLL | SWT.MULTI | SWT.FULL_SELECTION);
      viewer.getTree().setHeaderVisible(true);
      List<DbcProofObligation> columnProofObligations = addColumsnToViewer(viewer, viewerLayout, model);
      adapterFactory = new ComposedAdapterFactory(ComposedAdapterFactory.Descriptor.Registry.INSTANCE);
      adapterFactory.addAdapterFactory(new ResourceItemProviderAdapterFactory());
      adapterFactory.addAdapterFactory(new StatisticDbcmodelItemProviderAdapterFactory(columnProofObligations));
      adapterFactory.addAdapterFactory(new ReflectiveItemProviderAdapterFactory());
      viewer.setContentProvider(new AdapterFactoryContentProvider(adapterFactory));
      AdapterFactoryLabelProvider labelProvider = new AdapterFactoryLabelProvider(adapterFactory);
      labelProvider.setFireLabelUpdateNotifications(true);
      viewer.setLabelProvider(labelProvider);
      viewer.setInput(model);
      viewer.addDoubleClickListener(new IDoubleClickListener() {
         @Override
         public void doubleClick(DoubleClickEvent event) {
            handleDoubleClick(event);
         }
      });
      colorDecorator = new StatisticColorDecorator(viewer, 1, selectedObligations, adapterFactory);
      colorDecorator.initTreeItems();
      // Update UI
      layout();
   }

   /**
    * Handles a double click in the viewer.
    * @param event The event.
    */
   protected void handleDoubleClick(DoubleClickEvent event) {
      if (statisticProvider != null) {
         statisticProvider.select(viewer.getSelection());
      }
   }

   /**
    * When the model has changed.
    * @param msg The change {@link Notification}.
    */
   protected void handleModelChanged(Notification msg) {
      if (DbcmodelPackage.Literals.DBC_MODEL__PROOF_OBLIGATIONS.equals(msg.getFeature())) {
         if (Notification.ADD == msg.getEventType() || Notification.ADD_MANY == msg.getEventType() ||
             Notification.REMOVE == msg.getEventType() || Notification.REMOVE_MANY == msg.getEventType()) {
            updateViewer();
         }
      }
      else if (DbcmodelPackage.Literals.DBC_PROOF_OBLIGATION__OBLIGATION.equals(msg.getFeature())) {
         if (Notification.SET == msg.getEventType()) {
            updateColumnText(msg.getNotifier(), msg.getNewStringValue());
         }
      }
   }

   /**
    * Updates the column text on the column of {@link #viewer} that
    * has the given column data.
    * @param columnData The column data of the column to update.
    * @param newText The new text to set on the column.
    */
   protected void updateColumnText(Object columnData, String newText) {
      // Search column with the given column data.
      TreeColumn column = null;
      int i = 0;
      while (column == null && i < viewer.getTree().getColumnCount()) {
         TreeColumn currentColumn = viewer.getTree().getColumn(i);
         if (ObjectUtil.equal(columnData, currentColumn.getData())) {
            column = currentColumn;
         }
         i++;
      }
      // Update title
      if (column != null) {
         column.setText(newText);
      }
   }

   /**
    * Adds the columns to the viewer.
    * @param viewer The parent {@link TreeViewer}
    * @param viewerLayout The layout to arrange the columns in the {@link TreeViewer}.
    * @param model The {@link DbcModel} that contains the available proof obligations.
    */
   protected List<DbcProofObligation> addColumsnToViewer(TreeViewer viewer, TreeColumnLayout viewerLayout, DbcModel model) {
      TreeViewerColumn mainColumn = new TreeViewerColumn(viewer, SWT.NONE);
      mainColumn.getColumn().setText("Main");
      mainColumn.getColumn().setMoveable(true);
      viewerLayout.setColumnData(mainColumn.getColumn(), new ColumnWeightData(100));
      List<DbcProofObligation> result = new LinkedList<DbcProofObligation>();
      if (model != null) {
         for (DbcProofObligation obligation : model.getProofObligations()) {
            if (selectedObligations.contains(obligation)) {
               TreeViewerColumn column = new TreeViewerColumn(viewer, SWT.NONE);
               column.getColumn().setText(obligation.getObligation());
               column.getColumn().setData(obligation);
               column.getColumn().setMoveable(true);
               viewerLayout.setColumnData(column.getColumn(), new ColumnWeightData(10));
               observedObligations.add(obligation);
               obligation.eAdapters().add(modelListener);
               result.add(obligation);
            }
         }
      }
      return result;
   }
   
   /**
    * Removes the listener from all observed {@link ProofObligation} in
    * {@link #observedObligations}.
    */
   protected void removeListenerFromProofObligations() {
      for (DbcProofObligation obligation : observedObligations) {
         obligation.eAdapters().remove(modelListener);
      }
      observedObligations.clear();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      if (model != null) {
         model.eAdapters().remove(modelListener);
      }
      removeListenerFromProofObligations();
      if (colorDecorator != null) {
         colorDecorator.dispose();
      }
      if (adapterFactory != null) {
         adapterFactory.dispose();
      }
      selectedObligations.clear();
      super.dispose();
   }

   /**
    * Opens the dialog to select proof obligations.
    */
   public void openSelectProofObligationsDialog() {
      List<DbcProofObligation> newSelectedObligations = SelectProofObligationsWizard.open(getShell(), model.getProofObligations(), observedObligations);
      if (newSelectedObligations != null) {
         this.selectedObligations = newSelectedObligations;
         updateViewer();
      }
   }
}