package org.key_project.sed.ui.property;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ControlEvent;
import org.eclipse.swt.events.ControlListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.layout.RowData;
import org.eclipse.swt.layout.RowLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetWidgetFactory;
import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.annotation.ISEDAnnotationLink;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.ui.action.ISEDAnnotationLinkEditAction;
import org.key_project.sed.ui.provider.AnnotationLinkColorTableSynchronizer;
import org.key_project.sed.ui.provider.AnnotationLinkContentProvider;
import org.key_project.sed.ui.provider.AnnotationLinkLabelProvider;
import org.key_project.sed.ui.util.SEDImages;
import org.key_project.sed.ui.util.SEDUIUtil;
import org.key_project.sed.ui.util.SEDUIUtil.SEDAnnotationLinkActionDescription;
import org.key_project.util.eclipse.swt.SWTUtil;

/**
 * The {@link ISEDDebugNodeTabContent} shown in {@link AnnotationLinkPropertySection}.
 * @author Martin Hentschel
 */
public class AnnotationLinkTabComposite implements ISEDDebugNodeTabContent {
   /**
    * Contains all available action buttons.
    */
   private final List<Button> actionButtons = new LinkedList<Button>();

   /**
    * Shows the available annotations.
    */
   private TableViewer annoationLinksViewer;
   
   /**
    * The {@link IStructuredContentProvider} of {@link #annoationLinksViewer}.
    */
   private AnnotationLinkContentProvider annoationLinksContentProvider;
   
   /**
    * The {@link ITableLabelProvider} of {@link #annoationLinksViewer}.
    */
   private AnnotationLinkLabelProvider annotationLinksLabelProvider;
   
   /**
    * Ensures that the colors defined by an {@link ISEDAnnotation} are used in {@link #annoationLinksViewer}.
    */
   private AnnotationLinkColorTableSynchronizer annotationLinksColorSynchronizer;
   
   /**
    * The currently shown {@link ISEDDebugNode}.
    */
   private ISEDDebugNode node;

   /**
    * The {@link Button} to edit a selected {@link ISEDAnnotation}.
    */
   private Button editButton;
   
   /**
    * The {@link Button} to delete selected {@link ISEDAnnotation}s.
    */
   private Button deleteButton;
   
   /**
    * Context menu item of {@link #annoationLinksViewer} to edit the {@link ISEDAnnotationLink}.
    */
   private Action editAction;

   /**
    * Context menu item of {@link #annoationLinksViewer} to delete the {@link ISEDAnnotationLink}s.
    */
   private Action deleteAction;
   
   /**
    * Constructor.
    */
   public AnnotationLinkTabComposite() {
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void createComposite(final Composite parent, TabbedPropertySheetWidgetFactory factory) {
      final Composite composite = factory.createFlatFormComposite(parent);
      composite.setLayout(new GridLayout(1, false));
      // Add annotation debug target actions.
      final Composite actionComposite = factory.createFlatFormComposite(composite);
      actionComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      actionComposite.setLayout(new RowLayout());
      final Label separatorLabel;
      if (!SEDUIUtil.getAnnotationLinkActionDescriptions().isEmpty()) {
         for (final SEDAnnotationLinkActionDescription description : SEDUIUtil.getAnnotationLinkActionDescriptions()) {
            Button button = factory.createButton(actionComposite, description.getText(), SWT.PUSH);
            button.setToolTipText(description.getToolTipText());
            button.setEnabled(node != null);
            actionButtons.add(button);
            if (description.getImage() != null) {
               button.setImage(description.getImage());
            }
            if (description.getAction() != null) {
               button.addSelectionListener(new SelectionAdapter() {
                  @Override
                  public void widgetSelected(SelectionEvent e) {
                     description.getAction().run(parent.getShell(), node);
                  }
               });
            }
         }
         separatorLabel = factory.createSeparator(actionComposite, SWT.VERTICAL);
      }
      else {
         separatorLabel = null;
      }
      // Add edit buttons
      editButton = factory.createButton(actionComposite, "", SWT.PUSH);
      editButton.setToolTipText("Edit the selected annotation link.");
      editButton.setImage(SEDImages.getImage(SEDImages.ANNOTATION_EDIT));
      editButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            editAnnotationLink();
         }
      });
      if (separatorLabel != null) {
         // The resizeListener sets the correct layout data to ensure that the separator has the same height as the buttons
         ControlListener resizeListener = new ControlListener() {
            @Override
            public void controlResized(ControlEvent e) {
               separatorLabel.setLayoutData(new RowData(separatorLabel.getSize().x, editButton.getSize().y));
               actionComposite.setLayout(new RowLayout());
               actionComposite.layout();
               composite.layout();
               editButton.removeControlListener(this);
            }
            
            @Override
            public void controlMoved(ControlEvent e) {
            }
         };
         editButton.addControlListener(resizeListener);
      }
      deleteButton = factory.createButton(actionComposite, "", SWT.PUSH);
      deleteButton.setToolTipText("Delete selected annotation links.");
      deleteButton.setImage(SEDImages.getImage(SEDImages.ANNOTATION_DELETE));
      deleteButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            deleteAnnotationLinks();
         }
      });
      // Add annotation viewer
      annoationLinksViewer = new TableViewer(composite, SWT.BORDER | SWT.MULTI | SWT.V_SCROLL);
      annoationLinksViewer.getControl().setLayoutData(new GridData(GridData.FILL_BOTH));
      annoationLinksContentProvider = new AnnotationLinkContentProvider();
      annoationLinksViewer.setContentProvider(annoationLinksContentProvider);
      annoationLinksViewer.addSelectionChangedListener(new ISelectionChangedListener() {
         @Override
         public void selectionChanged(SelectionChangedEvent event) {
            updateEditButtonsEnablement();
         }
      });
      MenuManager annoationLinksViewerMenuManager = new MenuManager();
      editAction = new Action("&Edit", SEDImages.getImageDescriptor(SEDImages.ANNOTATION_EDIT)) {
         @Override
         public void run() {
            editAnnotationLink();
         }
      };
      annoationLinksViewerMenuManager.add(editAction);
      deleteAction = new Action("&Delete", SEDImages.getImageDescriptor(SEDImages.ANNOTATION_DELETE)) {
         @Override
         public void run() {
            deleteAnnotationLinks();
         }
      };
      annoationLinksViewerMenuManager.add(deleteAction);
      annoationLinksViewer.getControl().setMenu(annoationLinksViewerMenuManager.createContextMenu(annoationLinksViewer.getControl()));
      annoationLinksViewer.addDoubleClickListener(new IDoubleClickListener() {
         @Override
         public void doubleClick(DoubleClickEvent event) {
            handleDoubleClick(event);
         }
      });
      updateEditButtonsEnablement();
   }

   /**
    * A double click was performed on {@link #annoationLinksViewer}.
    * @param event The event.
    */
   protected void handleDoubleClick(DoubleClickEvent event) {
      editAnnotationLink();
   }

   /**
    * Edits the currently selected {@link ISEDAnnotationLink}.
    */
   public void editAnnotationLink() {
      Object obj = SWTUtil.getFirstElement(annoationLinksViewer.getSelection());
      if (obj instanceof ISEDAnnotationLink) {
         ISEDAnnotationLink link = (ISEDAnnotationLink)obj;
         ISEDAnnotationLinkEditAction action = SEDUIUtil.getAnnotationLinkEditAction(link.getSource().getType().getTypeId());
         if (action != null && action.canEdit(link)) {
            action.edit(editButton.getShell(), link);
         }
      }
   }
   
   /**
    * Deletes selected {@link ISEDAnnotationLink}s.
    */
   public void deleteAnnotationLinks() {
      Object[] selected = SWTUtil.toArray(annoationLinksViewer.getSelection());
      for (Object obj : selected) {
         if (obj instanceof ISEDAnnotationLink) {
            ISEDAnnotationLink link = (ISEDAnnotationLink)obj;
            link.delete();
         }
      }
   }

   /**
    * Updates the enabled state of the edit buttons.
    */
   protected void updateEditButtonsEnablement() {
      Object[] selected = SWTUtil.toArray(annoationLinksViewer.getSelection());
      // Compute enabled states
      boolean canDelete = false;
      boolean canEdit = false;
      int i = 0;
      while (i < selected.length && (!canDelete || !canEdit)) {
         if (selected[i] instanceof ISEDAnnotationLink) {
            ISEDAnnotationLink link = (ISEDAnnotationLink)selected[i];
            if (!canDelete && link.canDelete()) {
               canDelete = true;
            }
            if (!canEdit && SEDUIUtil.getAnnotationLinkEditAction(link.getSource().getType().getTypeId()) != null) {
               canEdit = true;
            }
         }
         i++;
      }
      // Update enabled states
      editButton.setEnabled(selected.length == 1 && canEdit);
      deleteButton.setEnabled(canDelete);
      editAction.setEnabled(selected.length == 1 && canEdit);
      deleteAction.setEnabled(canDelete);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void updateContent(ISEDDebugNode node) {
      this.node = node;
      if (annotationLinksLabelProvider != null) {
         annotationLinksLabelProvider.dispose();
      }
      if (annotationLinksColorSynchronizer != null) {
         annotationLinksColorSynchronizer.dispose();
      }
      annoationLinksViewer.setInput(node);
      annotationLinksLabelProvider = new AnnotationLinkLabelProvider(node);
      annoationLinksViewer.setLabelProvider(annotationLinksLabelProvider);
      annotationLinksColorSynchronizer = new AnnotationLinkColorTableSynchronizer(node, annoationLinksViewer);
      for (Button button : actionButtons) {
         button.setEnabled(node != null);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      if (annoationLinksContentProvider != null) {
         annoationLinksContentProvider.dispose();
      }
      if (annotationLinksLabelProvider != null) {
         annotationLinksLabelProvider.dispose();
      }
      if (annotationLinksColorSynchronizer != null) {
         annotationLinksColorSynchronizer.dispose();
      }
   }
}
