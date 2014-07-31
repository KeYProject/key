package org.key_project.sed.ui.property;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.debug.core.DebugEvent;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.IDebugEventSetListener;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.CLabel;
import org.eclipse.swt.layout.FormAttachment;
import org.eclipse.swt.layout.FormData;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.views.properties.tabbed.ISection;
import org.eclipse.ui.views.properties.tabbed.ITabbedPropertyConstants;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetPage;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetWidgetFactory;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.util.eclipse.job.AbstractDependingOnObjectsJob;
import org.key_project.util.eclipse.swt.SWTUtil;

/**
 * An {@link ISection} implementation to show statistics of an {@link ISEDDebugTarget}.
 * @author Martin Hentschel
 */
public class StatisticsPropertySection extends AbstractSEDDebugTargetPropertySection {
   /**
    * The {@link Composite} which shows {@link #composite}.
    */
   private Composite containerComposite;
   
   /**
    * The currently shown {@link Composite}.
    */
   private Composite composite;
   
   /**
    * The used {@link TabbedPropertySheetWidgetFactory}.
    */
   private TabbedPropertySheetWidgetFactory factory;

   /**
    * Listens for debug events.
    */
   private final IDebugEventSetListener debugListener = new IDebugEventSetListener() {
      @Override
      public void handleDebugEvents(DebugEvent[] events) {
         StatisticsPropertySection.this.handleDebugEvents(events);
      }
   };

   /**
    * {@inheritDoc}
    */
   @Override
   public void createControls(final Composite parent, TabbedPropertySheetPage aTabbedPropertySheetPage) {
      factory = aTabbedPropertySheetPage.getWidgetFactory();
      containerComposite = parent;
      refresh();
      DebugPlugin.getDefault().addDebugEventListener(debugListener);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void refresh() {
      final ISEDDebugTarget target = getDebugTarget();
      if (target != null) {
         showLabel("Please wait until statisitcs are computed.");
         AbstractDependingOnObjectsJob.cancelJobs(this);
         Job job = new AbstractDependingOnObjectsJob("Computing statistics", this, PlatformUI.getWorkbench()) {
            @Override
            protected IStatus run(final IProgressMonitor monitor) {
               try {
                  Map<String, String> statistics;
                  try {
                     statistics = target.computeStatistics(monitor);
                  }
                  catch (DebugException e) {
                     statistics = new LinkedHashMap<String, String>();
                     statistics.put("Error", e.getMessage());
                  }
                  final Map<String, String> statisticsToShow = statistics;
                  SWTUtil.checkCanceled(monitor);
                  containerComposite.getDisplay().asyncExec(new Runnable() {
                     @Override
                     public void run() {
                        if (!monitor.isCanceled()) {
                           recreateContent(statisticsToShow);
                        }
                     }
                  });
                  return Status.OK_STATUS;
               }
               catch (OperationCanceledException e) {
                  return Status.CANCEL_STATUS;
               }
            }
         };
         job.setSystem(true);
         job.schedule();
      }
      else {
         recreateContent(null);
      }
   }
   
   /**
    * When some {@link DebugEvent}s occurred.
    * @param events The {@link DebugEvent}s.
    */
   protected void handleDebugEvents(DebugEvent[] events) {
      for (DebugEvent event : events) {
         if (event.getSource() == getDebugTarget()) {
            containerComposite.getDisplay().asyncExec(new Runnable() {
               @Override
               public void run() {
                  refresh();
               }
            });
         }
      }
   }
   
   /**
    * Shows the given text.
    * @param text The text to show.
    */
   protected void showLabel(String text) {
      disposeContent();
      composite = factory.createFlatFormComposite(containerComposite);
      factory.createLabel(composite, text);
      containerComposite.pack();
      containerComposite.layout();
   }
   
   /**
    * Recreates the shown content.
    */
   protected void recreateContent(Map<String, String> statistics) {
      disposeContent();
      createContent(statistics);
      containerComposite.pack();
      containerComposite.layout();
   }

   /**
    * Disposes the currently shown content.
    */
   protected void disposeContent() {
      if (composite != null && !composite.isDisposed()) {
         composite.setVisible(false);
         composite.dispose();
         composite = null;
      }
   }
   
   /**
    * Creates new content to show.
    * @param statistics The statistics to show.
    */
   protected void createContent(Map<String, String> statistics) {
      final int LABEL_WIDTH = 210;
      composite = factory.createFlatFormComposite(containerComposite);
      Control lastControl = null;
      if (statistics != null) {
         for (Entry<String, String> entry : statistics.entrySet()) {
            Text valueText = factory.createText(composite, entry.getValue());
            valueText.setEditable(false);
            FormData data = new FormData();
            data.left = new FormAttachment(0, LABEL_WIDTH);
            data.right = new FormAttachment(100, 0);
            data.top = new FormAttachment(lastControl, 0, ITabbedPropertyConstants.VSPACE);
            valueText.setLayoutData(data);
            lastControl = valueText;
            
            CLabel workspacePathLabel = factory.createCLabel(composite, entry.getKey());
            data = new FormData();
            data.left = new FormAttachment(0, 0);
            data.right = new FormAttachment(valueText, -ITabbedPropertyConstants.HSPACE);
            data.top = new FormAttachment(valueText, 0, SWT.CENTER);
            workspacePathLabel.setLayoutData(data);
         }
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      DebugPlugin.getDefault().removeDebugEventListener(debugListener);
      super.dispose();
   }
}
