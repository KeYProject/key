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

package de.hentschel.visualdbc.dbcmodel.diagram.part;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Status;
import org.eclipse.emf.common.notify.AdapterFactory;
import org.eclipse.emf.edit.provider.ComposedAdapterFactory;
import org.eclipse.emf.edit.provider.IItemLabelProvider;
import org.eclipse.emf.edit.provider.ReflectiveItemProviderAdapterFactory;
import org.eclipse.emf.edit.provider.resource.ResourceItemProviderAdapterFactory;
import org.eclipse.emf.edit.ui.provider.ExtendedImageRegistry;
import org.eclipse.gmf.runtime.diagram.core.preferences.PreferencesHint;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

import de.hentschel.visualdbc.dbcmodel.diagram.edit.policies.DbCBaseItemSemanticEditPolicy;
import de.hentschel.visualdbc.dbcmodel.diagram.expressions.DbCOCLFactory;
import de.hentschel.visualdbc.dbcmodel.diagram.providers.ElementInitializers;
import de.hentschel.visualdbc.dbcmodel.provider.DbcmodelItemProviderAdapterFactory;

/**
 * @generated
 */
public class DbCDiagramEditorPlugin extends AbstractUIPlugin {

   /**
    * @generated
    */
   public static final String ID = "de.hentschel.visualdbc.dbcmodel.diagram"; //$NON-NLS-1$

   /**
    * @generated
    */
   public static final PreferencesHint DIAGRAM_PREFERENCES_HINT = new PreferencesHint(
         ID);

   /**
    * @generated
    */
   private static DbCDiagramEditorPlugin instance;

   /**
    * @generated
    */
   private ComposedAdapterFactory adapterFactory;

   /**
    * @generated
    */
   private DbCDocumentProvider documentProvider;

   /**
    * @generated
    */
   private DbCBaseItemSemanticEditPolicy.LinkConstraints linkConstraints;

   /**
    * @generated
    */
   private ElementInitializers initializers;

   /**
    * @generated
    */
   private DbCOCLFactory oclFactory;

   /**
    * @generated
    */
   public DbCDiagramEditorPlugin() {
   }

   /**
    * @generated
    */
   public void start(BundleContext context) throws Exception {
      super.start(context);
      instance = this;
      PreferencesHint.registerPreferenceStore(DIAGRAM_PREFERENCES_HINT,
            getPreferenceStore());
      adapterFactory = createAdapterFactory();
   }

   /**
    * @generated
    */
   public void stop(BundleContext context) throws Exception {
      adapterFactory.dispose();
      adapterFactory = null;
      linkConstraints = null;
      initializers = null;
      oclFactory = null;
      instance = null;
      super.stop(context);
   }

   /**
    * @generated
    */
   public static DbCDiagramEditorPlugin getInstance() {
      return instance;
   }

   /**
    * @generated
    */
   protected ComposedAdapterFactory createAdapterFactory() {
      ArrayList<AdapterFactory> factories = new ArrayList<AdapterFactory>();
      fillItemProviderFactories(factories);
      return new ComposedAdapterFactory(factories);
   }

   /**
    * @generated
    */
   protected void fillItemProviderFactories(List<AdapterFactory> factories) {
      factories.add(new DbcmodelItemProviderAdapterFactory());
      factories.add(new ResourceItemProviderAdapterFactory());
      factories.add(new ReflectiveItemProviderAdapterFactory());
   }

   /**
    * @generated
    */
   public AdapterFactory getItemProvidersAdapterFactory() {
      return adapterFactory;
   }

   /**
    * @generated
    */
   public ImageDescriptor getItemImageDescriptor(Object item) {
      IItemLabelProvider labelProvider = (IItemLabelProvider) adapterFactory
            .adapt(item, IItemLabelProvider.class);
      if (labelProvider != null) {
         return ExtendedImageRegistry.getInstance().getImageDescriptor(
               labelProvider.getImage(item));
      }
      return null;
   }

   /**
    * Returns an image descriptor for the image file at the given
    * plug-in relative path.
    *
    * @generated
    * @param path the path
    * @return the image descriptor
    */
   public static ImageDescriptor getBundledImageDescriptor(String path) {
      return AbstractUIPlugin.imageDescriptorFromPlugin(ID, path);
   }

   /**
    * Respects images residing in any plug-in. If path is relative,
    * then this bundle is looked up for the image, otherwise, for absolute 
    * path, first segment is taken as id of plug-in with image
    *
    * @generated
    * @param path the path to image, either absolute (with plug-in id as first segment), or relative for bundled images
    * @return the image descriptor
    */
   public static ImageDescriptor findImageDescriptor(String path) {
      final IPath p = new Path(path);
      if (p.isAbsolute() && p.segmentCount() > 1) {
         return AbstractUIPlugin.imageDescriptorFromPlugin(p.segment(0), p
               .removeFirstSegments(1).makeAbsolute().toString());
      }
      else {
         return getBundledImageDescriptor(p.makeAbsolute().toString());
      }
   }

   /**
    * Returns an image for the image file at the given plug-in relative path.
    * Client do not need to dispose this image. Images will be disposed automatically.
    *
    * @generated
    * @param path the path
    * @return image instance
    */
   public Image getBundledImage(String path) {
      Image image = getImageRegistry().get(path);
      if (image == null) {
         getImageRegistry().put(path, getBundledImageDescriptor(path));
         image = getImageRegistry().get(path);
      }
      return image;
   }

   /**
    * Returns string from plug-in's resource bundle
    *
    * @generated
    */
   public static String getString(String key) {
      return Platform.getResourceString(getInstance().getBundle(), "%" + key); //$NON-NLS-1$
   }

   /**
    * @generated
    */
   public DbCDocumentProvider getDocumentProvider() {
      if (documentProvider == null) {
         documentProvider = new DbCDocumentProvider();
      }
      return documentProvider;
   }

   /**
    * @generated
    */
   public DbCBaseItemSemanticEditPolicy.LinkConstraints getLinkConstraints() {
      return linkConstraints;
   }

   /**
    * @generated
    */
   public void setLinkConstraints(
         DbCBaseItemSemanticEditPolicy.LinkConstraints lc) {
      this.linkConstraints = lc;
   }

   /**
    * @generated
    */
   public ElementInitializers getElementInitializers() {
      return initializers;
   }

   /**
    * @generated
    */
   public void setElementInitializers(ElementInitializers i) {
      this.initializers = i;
   }

   /**
    * @generated
    */
   public DbCOCLFactory getDbCOCLFactory() {
      return oclFactory;
   }

   /**
    * @generated
    */
   public void setDbCOCLFactory(DbCOCLFactory f) {
      this.oclFactory = f;
   }

   /**
    * @generated
    */
   public void logError(String error) {
      logError(error, null);
   }

   /**
    * @generated
    */
   public void logError(String error, Throwable throwable) {
      if (error == null && throwable != null) {
         error = throwable.getMessage();
      }
      getLog().log(
            new Status(IStatus.ERROR, DbCDiagramEditorPlugin.ID, IStatus.OK,
                  error, throwable));
      debug(error, throwable);
   }

   /**
    * @generated
    */
   public void logInfo(String message) {
      logInfo(message, null);
   }

   /**
    * @generated
    */
   public void logInfo(String message, Throwable throwable) {
      if (message == null && throwable != null) {
         message = throwable.getMessage();
      }
      getLog().log(
            new Status(IStatus.INFO, DbCDiagramEditorPlugin.ID, IStatus.OK,
                  message, throwable));
      debug(message, throwable);
   }

   /**
    * @generated
    */
   private void debug(String message, Throwable throwable) {
      if (!isDebugging()) {
         return;
      }
      if (message != null) {
         System.err.println(message);
      }
      if (throwable != null) {
         throwable.printStackTrace();
      }
   }
}