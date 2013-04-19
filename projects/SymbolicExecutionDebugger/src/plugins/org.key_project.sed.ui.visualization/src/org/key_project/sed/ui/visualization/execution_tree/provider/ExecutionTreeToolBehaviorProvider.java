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

package org.key_project.sed.ui.visualization.execution_tree.provider;

import java.net.URL;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtension;
import org.eclipse.core.runtime.IExtensionPoint;
import org.eclipse.core.runtime.IExtensionRegistry;
import org.eclipse.core.runtime.Platform;
import org.eclipse.graphiti.dt.IDiagramTypeProvider;
import org.eclipse.graphiti.features.context.ICustomContext;
import org.eclipse.graphiti.features.context.IPictogramElementContext;
import org.eclipse.graphiti.features.context.impl.CustomContext;
import org.eclipse.graphiti.features.custom.ICustomFeature;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.palette.IPaletteCompartmentEntry;
import org.eclipse.graphiti.tb.ContextButtonEntry;
import org.eclipse.graphiti.tb.ContextMenuEntry;
import org.eclipse.graphiti.tb.DefaultToolBehaviorProvider;
import org.eclipse.graphiti.tb.IContextButtonEntry;
import org.eclipse.graphiti.tb.IContextButtonPadData;
import org.eclipse.graphiti.tb.IContextMenuEntry;
import org.eclipse.graphiti.tb.IToolBehaviorProvider;
import org.eclipse.graphiti.ui.internal.GraphitiUIPlugin;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.swt.graphics.Image;
import org.key_project.sed.ui.visualization.execution_tree.feature.DebugNodeResumeFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.DebugNodeStepIntoFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.DebugNodeStepOverFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.DebugNodeStepReturnFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.DebugNodeSuspendFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.DebugNodeTerminateFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.DebugNodeVisualizeStateFeature;
import org.key_project.sed.ui.visualization.util.ICustomFeatureFactory;
import org.key_project.sed.ui.visualization.util.LogUtil;
import org.key_project.util.java.CollectionUtil;
import org.osgi.framework.Bundle;

/**
 * {@link IToolBehaviorProvider} specific implementation for
 * execution tree diagrams.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class ExecutionTreeToolBehaviorProvider extends DefaultToolBehaviorProvider {
   /**
    * ID of the used extension point.
    */
   public static final String CONTEXT_ITEM_EXTENSION_POINT = "org.key_project.sed.ui.visualization.executionTree.contextMenuEntries";
   
   /**
    * Indicates that the diagram is read-only or editable.
    */
   private boolean readOnly = false;
   
   /**
    * Constructor.
    * @param diagramTypeProvider The diagram type provider for that this {@link IToolBehaviorProvider} is used.
    */
   public ExecutionTreeToolBehaviorProvider(IDiagramTypeProvider diagramTypeProvider) {
      super(diagramTypeProvider);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isConnectionSelectionEnabled() {
      return !isReadOnly();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IContextButtonPadData getContextButtonPad(IPictogramElementContext context) {
      IContextButtonPadData data = super.getContextButtonPad(context);
      if (isReadOnly()) {
         data.getGenericContextButtons().clear();
         List<IContextButtonEntry> epEntries = collectContextButtonEntriesFromExtensionPoint(isReadOnly(), context);
         data.getGenericContextButtons().addAll(epEntries);
         data.getGenericContextButtons().add(createCustomContextButtonEntry(new DebugNodeVisualizeStateFeature(getFeatureProvider()), context, "Visualize State", null, IExecutionTreeImageConstants.IMG_VISUALIZE_STATE));

         data.getGenericContextButtons().add(createCustomContextButtonEntry(new DebugNodeStepReturnFeature(getFeatureProvider()), context, "Step Return", null, IExecutionTreeImageConstants.IMG_STEP_RETURN));
         data.getGenericContextButtons().add(createCustomContextButtonEntry(new DebugNodeStepOverFeature(getFeatureProvider()), context, "Step Over", null, IExecutionTreeImageConstants.IMG_STEP_OVER));
         data.getGenericContextButtons().add(createCustomContextButtonEntry(new DebugNodeStepIntoFeature(getFeatureProvider()), context, "Step Into", null, IExecutionTreeImageConstants.IMG_STEP_INTO));

         data.getGenericContextButtons().add(createCustomContextButtonEntry(new DebugNodeTerminateFeature(getFeatureProvider()), context, "Terminate", null, IExecutionTreeImageConstants.IMG_TERMINATE));
         data.getGenericContextButtons().add(createCustomContextButtonEntry(new DebugNodeSuspendFeature(getFeatureProvider()), context, "Suspend", null, IExecutionTreeImageConstants.IMG_SUSPEND));
         data.getGenericContextButtons().add(createCustomContextButtonEntry(new DebugNodeResumeFeature(getFeatureProvider()), context, "Resume", null, IExecutionTreeImageConstants.IMG_RESUME));
      }
      else {
         List<IContextButtonEntry> epEntries = collectContextButtonEntriesFromExtensionPoint(isReadOnly(), context);
         data.getGenericContextButtons().addAll(epEntries);
      }
      return data;
   }

   /**
    * Creates an {@link IContextButtonEntry} which executes an {@link ICustomFeature}.
    * @param feature The {@link ICustomFeature} to execute.
    * @param context The parent {@link IPictogramElementContext}.
    * @param text The text.
    * @param description The description.
    * @param iconId The icon id.
    * @return The created {@link IContextButtonEntry}.
    */
   protected IContextButtonEntry createCustomContextButtonEntry(ICustomFeature feature, IPictogramElementContext context, String text, String description, String iconId) {
      IContextButtonEntry entry = new ContextButtonEntry(feature, new CustomContext(new PictogramElement[] {context.getPictogramElement()}));
      entry.setDescription(description);
      entry.setText(text);
      entry.setIconId(iconId);
      return entry;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IContextMenuEntry[] getContextMenu(ICustomContext context) {
      IContextMenuEntry[] menuEntries = super.getContextMenu(context);
      List<IContextMenuEntry> result = new LinkedList<IContextMenuEntry>();
      CollectionUtil.addAll(result, menuEntries);
      if (isReadOnly()) {
         result.add(createCustomContextMenuEntry(new DebugNodeResumeFeature(getFeatureProvider()), context, "Resume", null, IExecutionTreeImageConstants.IMG_RESUME));
         result.add(createCustomContextMenuEntry(new DebugNodeSuspendFeature(getFeatureProvider()), context, "Suspend", null, IExecutionTreeImageConstants.IMG_SUSPEND));
         result.add(createCustomContextMenuEntry(new DebugNodeTerminateFeature(getFeatureProvider()), context, "Terminate", null, IExecutionTreeImageConstants.IMG_TERMINATE));

         result.add(createCustomContextMenuEntry(new DebugNodeStepOverFeature(getFeatureProvider()), context, "Step Over", null, IExecutionTreeImageConstants.IMG_STEP_OVER));
         result.add(createCustomContextMenuEntry(new DebugNodeStepIntoFeature(getFeatureProvider()), context, "Step Into", null, IExecutionTreeImageConstants.IMG_STEP_INTO));
         result.add(createCustomContextMenuEntry(new DebugNodeStepReturnFeature(getFeatureProvider()), context, "Step Return", null, IExecutionTreeImageConstants.IMG_STEP_RETURN));

         result.add(createCustomContextMenuEntry(new DebugNodeVisualizeStateFeature(getFeatureProvider()), context, "Visualize State", null, IExecutionTreeImageConstants.IMG_VISUALIZE_STATE));
      }
      List<IContextMenuEntry> epEntries = collectContextMenuEntriesFromExtensionPoint(isReadOnly(), context);
      result.addAll(epEntries);
      return result.toArray(new IContextMenuEntry[result.size()]);
   }
   
   /**
    * Lists additional {@link IContextMenuEntry}s from the extension point.
    * @param readOnly {@code true} read-only mode, {@code false} editable mode.
    * @param context The {@link ICustomContext} to use.
    * @return The found {@link IContextMenuEntry}s.
    */
   protected List<IContextMenuEntry> collectContextMenuEntriesFromExtensionPoint(boolean readOnly, ICustomContext context) {
      List<IContextMenuEntry> result = new LinkedList<IContextMenuEntry>();
      IExtensionRegistry registry = Platform.getExtensionRegistry();
      if (registry != null) {
         IExtensionPoint point = registry.getExtensionPoint(CONTEXT_ITEM_EXTENSION_POINT);
         if (point != null) {
            // Analyze the extension point
            IExtension[] extensions = point.getExtensions();
            for (IExtension extension : extensions) {
               IConfigurationElement[] configElements = extension.getConfigurationElements();
               for (IConfigurationElement configElement : configElements) {
                  try {
                     if (("ALWAYS".equals(configElement.getAttribute("modes")) ||
                         (readOnly ? "READ_ONLY" : "EDITABLE").equals(configElement.getAttribute("modes"))) &&
                         Boolean.valueOf(configElement.getAttribute("inMenu"))) {
                        makeSureThatImageIdExist(configElement);
                        ICustomFeatureFactory factory = (ICustomFeatureFactory)configElement.createExecutableExtension("factory");
                        result.add(createCustomContextMenuEntry(factory.createFeature(getFeatureProvider()), context, configElement.getAttribute("text"), configElement.getAttribute("description"), configElement.getAttribute("iconId")));
                     }
                  }
                  catch (Exception e) {
                     LogUtil.getLogger().logError(e);
                  }
               }
            }
         }
         else {
            LogUtil.getLogger().logError("Extension point \"" + CONTEXT_ITEM_EXTENSION_POINT + "\" doesn't exist.");
         }
      }
      return result;
   }

   /**
    * Lists additional {@link IContextButtonEntry}s from the extension point.
    * @param readOnly {@code true} read-only mode, {@code false} editable mode.
    * @param context The {@link IPictogramElementContext} to use.
    * @return The found {@link IContextButtonEntry}s.
    */
   protected List<IContextButtonEntry> collectContextButtonEntriesFromExtensionPoint(boolean readOnly, IPictogramElementContext context) {
      List<IContextButtonEntry> result = new LinkedList<IContextButtonEntry>();
      IExtensionRegistry registry = Platform.getExtensionRegistry();
      if (registry != null) {
         IExtensionPoint point = registry.getExtensionPoint(CONTEXT_ITEM_EXTENSION_POINT);
         if (point != null) {
            // Analyze the extension point
            IExtension[] extensions = point.getExtensions();
            for (IExtension extension : extensions) {
               IConfigurationElement[] configElements = extension.getConfigurationElements();
               for (IConfigurationElement configElement : configElements) {
                  try {
                     if (("ALWAYS".equals(configElement.getAttribute("modes")) ||
                         (readOnly ? "READ_ONLY" : "EDITABLE").equals(configElement.getAttribute("modes"))) &&
                         Boolean.valueOf(configElement.getAttribute("inMenu"))) {
                        makeSureThatImageIdExist(configElement);
                        ICustomFeatureFactory factory = (ICustomFeatureFactory)configElement.createExecutableExtension("factory");
                        result.add(createCustomContextButtonEntry(factory.createFeature(getFeatureProvider()), context, configElement.getAttribute("text"), configElement.getAttribute("description"), configElement.getAttribute("iconId")));
                     }
                  }
                  catch (Exception e) {
                     LogUtil.getLogger().logError(e);
                  }
               }
            }
         }
         else {
            LogUtil.getLogger().logError("Extension point \"" + CONTEXT_ITEM_EXTENSION_POINT + "\" doesn't exist.");
         }
      }
      return result;
   }
   
   /**
    * Makes sure that an {@link Image} exists for the defined image ID.
    * @param configElement The {@link IConfigurationElement} which provides the image.
    */
   protected void makeSureThatImageIdExist(IConfigurationElement configElement) {
      String imageKey = configElement.getAttribute("iconId");
      if (GraphitiUIPlugin.getDefault().getImageRegistry().getDescriptor(imageKey) == null) {
         Bundle bundle = Platform.getBundle(configElement.getContributor().getName());
         URL url = bundle.getResource(configElement.getAttribute("icon"));
         GraphitiUIPlugin.getDefault().getImageRegistry().put(imageKey, ImageDescriptor.createFromURL(url));
      }
   }

   /**
    * Creates an {@link IContextMenuEntry} which executes an {@link ICustomFeature}.
    * @param feature The {@link ICustomFeature} to execute.
    * @param context The {@link ICustomContext} to execute.
    * @param text The text.
    * @param description The description.
    * @param iconId The icon id.
    * @return The created {@link IContextMenuEntry}.
    */
   protected IContextMenuEntry createCustomContextMenuEntry(ICustomFeature feature, ICustomContext context, String text, String description, String iconId) {
      IContextMenuEntry entry = new ContextMenuEntry(feature, context);
      entry.setDescription(description);
      entry.setText(text);
      entry.setIconId(iconId);
      return entry;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IPaletteCompartmentEntry[] getPalette() {
      List<IPaletteCompartmentEntry> result = new LinkedList<IPaletteCompartmentEntry>();
      IPaletteCompartmentEntry[] entries = super.getPalette();
      for (IPaletteCompartmentEntry entry : entries) {
         if (!CollectionUtil.isEmpty(entry.getToolEntries())) { // Filter out empty entries
            result.add(entry);
         }
      }
      return result.toArray(new IPaletteCompartmentEntry[result.size()]);
   }

   /**
    * Checks if the diagram is read-only or editable.
    * @return {@code true} read-only, {@code false} editable.
    */
   public boolean isReadOnly() {
      return readOnly;
   }

   /**
    * Defines if the diagram is read-only or editable.
    * @param readOnly {@code true} read-only, {@code false} editable.
    */
   public void setReadOnly(boolean readOnly) {
      this.readOnly = readOnly;
   }
}