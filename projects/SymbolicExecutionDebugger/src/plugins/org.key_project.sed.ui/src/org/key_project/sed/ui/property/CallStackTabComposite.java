package org.key_project.sed.ui.property;

import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.internal.ui.viewers.model.provisional.PresentationContext;
import org.eclipse.debug.internal.ui.viewers.model.provisional.TreeModelViewer;
import org.eclipse.debug.ui.IDebugUIConstants;
import org.eclipse.debug.ui.IDebugView;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.FormAttachment;
import org.eclipse.swt.layout.FormData;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.views.properties.tabbed.ITabbedPropertyConstants;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetWidgetFactory;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.util.ISEDConstants;
import org.key_project.sed.ui.util.LogUtil;
import org.key_project.sed.ui.util.SEDUIUtil;
import org.key_project.util.eclipse.WorkbenchUtil;

/**
 * This composite provides the content shown in {@link CallStackPropertySection}
 * and in {@code GraphitiCallStackPropertySection}.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class CallStackTabComposite extends AbstractSEDDebugNodeTabComposite {
   /**
    * Shows the name of the current node.
    */
   private Group viewerGroup;
   
   /**
    * Shows the call stack {@link ISEDDebugNode#getCallStack()}.
    */
   private TreeModelViewer viewer;
   
   /**
    * Constructor.
    * @param parent The parent {@link Composite}.
    * @param style The style to use.
    * @param factory The {@link TabbedPropertySheetWidgetFactory} to use.
    */
   public CallStackTabComposite(Composite parent, int style, TabbedPropertySheetWidgetFactory factory) {
      super(parent, style);
      setLayout(new FillLayout());
      
      Composite composite = factory.createFlatFormComposite(this);
      
      viewerGroup = factory.createGroup(composite, "Call stack");
      viewerGroup.setLayout(new FillLayout());
      FormData data = new FormData();
      data.left = new FormAttachment(0, 0);
      data.right = new FormAttachment(100, 0);
      data.top = new FormAttachment(0, ITabbedPropertyConstants.VSPACE);
      viewerGroup.setLayoutData(data);
      
      viewer = new TreeModelViewer(viewerGroup, SWT.MULTI | SWT.H_SCROLL | SWT.V_SCROLL | SWT.VIRTUAL, new PresentationContext(ISEDConstants.ID_CALL_STACK));
      viewer.addDoubleClickListener(new IDoubleClickListener() {
         @Override
         public void doubleClick(DoubleClickEvent event) {
            handleDoubleClick(event);
         }
      });
   }

   /**
    * When a double click on an stack entry was done.
    * @param event The event.
    */
   protected void handleDoubleClick(DoubleClickEvent event) {
      IViewPart debugView = WorkbenchUtil.findView(IDebugUIConstants.ID_DEBUG_VIEW);
      if (debugView instanceof IDebugView) {
         SEDUIUtil.selectInDebugView(WorkbenchUtil.getActivePart(), (IDebugView)debugView, viewer.getSelection());
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void updateContent(ISEDDebugNode node) {
      String nodeText = "Call stack";
      try {
         if (node != null) {
            nodeText = "Call stack of: " + node.getName();
         }
      }
      catch (DebugException e) {
         LogUtil.getLogger().logError(e);
      }
      viewer.setInput(node);
      viewerGroup.setText(nodeText);
   }
}
