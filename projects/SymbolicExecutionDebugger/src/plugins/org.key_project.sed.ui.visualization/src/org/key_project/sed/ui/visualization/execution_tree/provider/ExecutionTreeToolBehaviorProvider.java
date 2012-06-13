package org.key_project.sed.ui.visualization.execution_tree.provider;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.graphiti.dt.IDiagramTypeProvider;
import org.eclipse.graphiti.features.context.IPictogramElementContext;
import org.eclipse.graphiti.features.context.impl.CustomContext;
import org.eclipse.graphiti.features.custom.ICustomFeature;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.palette.IPaletteCompartmentEntry;
import org.eclipse.graphiti.tb.ContextButtonEntry;
import org.eclipse.graphiti.tb.DefaultToolBehaviorProvider;
import org.eclipse.graphiti.tb.IContextButtonEntry;
import org.eclipse.graphiti.tb.IContextButtonPadData;
import org.eclipse.graphiti.tb.IToolBehaviorProvider;
import org.key_project.sed.ui.visualization.execution_tree.feature.DebugNodeResumeFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.DebugNodeStepIntoFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.DebugNodeStepOverFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.DebugNodeStepReturnFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.DebugNodeSuspendFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.DebugNodeTerminateFeature;
import org.key_project.util.java.CollectionUtil;

/**
 * {@link IToolBehaviorProvider} specific implementation for
 * execution tree diagrams.
 * @author Martin Hentschel
 */
public class ExecutionTreeToolBehaviorProvider extends DefaultToolBehaviorProvider {
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
      if (!isReadOnly()) {
         return super.getContextButtonPad(context);
      }
      else {
         IContextButtonPadData data = super.getContextButtonPad(context);
         data.getGenericContextButtons().clear();
         data.getGenericContextButtons().add(createCustomEntry(new DebugNodeStepReturnFeature(getFeatureProvider()), context, "Step Return", null, IExecutionTreeImageConstants.IMG_STEP_RETURN));
         data.getGenericContextButtons().add(createCustomEntry(new DebugNodeStepOverFeature(getFeatureProvider()), context, "Step Over", null, IExecutionTreeImageConstants.IMG_STEP_OVER));
         data.getGenericContextButtons().add(createCustomEntry(new DebugNodeStepIntoFeature(getFeatureProvider()), context, "Step Into", null, IExecutionTreeImageConstants.IMG_STEP_INTO));

         data.getGenericContextButtons().add(createCustomEntry(new DebugNodeTerminateFeature(getFeatureProvider()), context, "Terminate", null, IExecutionTreeImageConstants.IMG_TERMINATE));
         data.getGenericContextButtons().add(createCustomEntry(new DebugNodeSuspendFeature(getFeatureProvider()), context, "Suspend", null, IExecutionTreeImageConstants.IMG_SUSPEND));
         data.getGenericContextButtons().add(createCustomEntry(new DebugNodeResumeFeature(getFeatureProvider()), context, "Resume", null, IExecutionTreeImageConstants.IMG_RESUME));
         return data;
      }
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
   protected IContextButtonEntry createCustomEntry(ICustomFeature feature, IPictogramElementContext context, String text, String description, String iconId) {
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
