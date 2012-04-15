package org.key_project.sed.ui.visualization.execution_tree.provider;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.graphiti.dt.IDiagramTypeProvider;
import org.eclipse.graphiti.palette.IPaletteCompartmentEntry;
import org.eclipse.graphiti.tb.DefaultToolBehaviorProvider;
import org.eclipse.graphiti.tb.IToolBehaviorProvider;
import org.key_project.util.java.CollectionUtil;

/**
 * {@link IToolBehaviorProvider} specific implementation for
 * execution tree diagrams.
 * @author Martin Hentschel
 */
public class ExecutionTreeToolBehaviorProvider extends DefaultToolBehaviorProvider {
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
}
