package org.key_project.sed.ui.property;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.viewers.CheckboxTableViewer;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.SelectionChangedEvent;
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
import org.eclipse.ui.views.properties.tabbed.ISection;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetPage;
import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.annotation.ISEDAnnotationLink;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.ui.dialog.AnnotationLinksDialog;
import org.key_project.sed.ui.provider.AnnotationCheckedStateSynchronizer;
import org.key_project.sed.ui.provider.AnnotationColorTableSynchronizer;
import org.key_project.sed.ui.provider.AnnotationContentProvider;
import org.key_project.sed.ui.provider.AnnotationLabelProvider;
import org.key_project.sed.ui.util.SEDImages;
import org.key_project.sed.ui.util.SEDUIUtil;
import org.key_project.sed.ui.util.SEDUIUtil.SEDAnnotationActionDescription;
import org.key_project.sed.ui.wizard.EditWizard;
import org.key_project.util.eclipse.swt.SWTUtil;

/**
 * An {@link ISection} implementation to edit the {@link ISEDAnnotation}s
 * of an {@link ISEDDebugTarget}.
 * @author Martin Hentschel
 */
public class AnnotationPropertySection extends AbstractSEDDebugTargetPropertySection {
   /**
    * Contains all available action buttons.
    */
   private final List<Button> actionButtons = new LinkedList<Button>();

   /**
    * Shows the available annotations.
    */
   private CheckboxTableViewer annoationsViewer;
   
   /**
    * The {@link IStructuredContentProvider} of {@link #annoationsViewer}.
    */
   private AnnotationContentProvider annoationsContentProvider;
   
   /**
    * The {@link ITableLabelProvider} of {@link #annoationsViewer}.
    */
   private AnnotationLabelProvider annotationsLabelProvider;
   
   /**
    * The {@link AnnotationCheckedStateSynchronizer} used to synchronize the checked states of {@link #annoationsViewer} with {@link ISEDAnnotation#isEnabled()}.
    */
   private AnnotationCheckedStateSynchronizer annotationsSelectionSynchronizer;
   
   /**
    * Ensures that the colors defined by an {@link ISEDAnnotation} are used in {@link #annoationsViewer}.
    */
   private AnnotationColorTableSynchronizer annotationsColorSynchronizer;
   
   /**
    * The currently shown {@link ISEDDebugTarget}.
    */
   private ISEDDebugTarget target;

   /**
    * The {@link Button} to edit a selected {@link ISEDAnnotation}.
    */
   private Button editButton;
   
   /**
    * The {@link Button} to move selected {@link ISEDAnnotation}s up.
    */
   private Button upButton;

   /**
    * The {@link Button} to move selected {@link ISEDAnnotation}s down.
    */
   private Button downButton;
   
   /**
    * The {@link Button} to delete selected {@link ISEDAnnotation}s.
    */
   private Button deleteButton;
   
   /**
    * The {@link Button} to show all links of an {@link ISEDAnnotation}.
    */
   private Button linksButton;
   
   /**
    * Context menu item of {@link #annoationsViewer} to edit the {@link ISEDAnnotation}.
    */
   private Action editAction;

   /**
    * Context menu item of {@link #annoationsViewer} to move the {@link ISEDAnnotation}s up.
    */
   private Action upAction;

   /**
    * Context menu item of {@link #annoationsViewer} to move the {@link ISEDAnnotation}s down.
    */
   private Action downAction;

   /**
    * Context menu item of {@link #annoationsViewer} to show {@link ISEDAnnotationLink}s of the {@link ISEDAnnotation}.
    */
   private Action linksAction;

   /**
    * Context menu item of {@link #annoationsViewer} to delete the {@link ISEDAnnotation}s.
    */
   private Action deleteAction;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void createControls(final Composite parent, TabbedPropertySheetPage aTabbedPropertySheetPage) {
      super.createControls(parent, aTabbedPropertySheetPage);
      final Composite composite = getWidgetFactory().createFlatFormComposite(parent);
      composite.setLayout(new GridLayout(1, false));
      // Add annotation debug target actions.
      Composite actionComposite = getWidgetFactory().createFlatFormComposite(composite);
      actionComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      actionComposite.setLayout(new RowLayout());
      final Label separatorLabel;
      if (!SEDUIUtil.getAnnotationActionDescriptions().isEmpty()) {
         for (final SEDAnnotationActionDescription description : SEDUIUtil.getAnnotationActionDescriptions()) {
            Button button = getWidgetFactory().createButton(actionComposite, description.getText(), SWT.PUSH);
            button.setToolTipText(description.getToolTipText());
            button.setEnabled(target != null);
            actionButtons.add(button);
            if (description.getImage() != null) {
               button.setImage(description.getImage());
            }
            if (description.getAction() != null) {
               button.addSelectionListener(new SelectionAdapter() {
                  @Override
                  public void widgetSelected(SelectionEvent e) {
                     description.getAction().run(parent.getShell(), target);
                  }
               });
            }
         }
         separatorLabel = getWidgetFactory().createSeparator(actionComposite, SWT.VERTICAL);
      }
      else {
         separatorLabel = null;
      }
      // Add edit buttons
      editButton = getWidgetFactory().createButton(actionComposite, "", SWT.PUSH);
      editButton.setToolTipText("Edit the selected annotation.");
      editButton.setImage(SEDImages.getImage(SEDImages.ANNOTATION_EDIT));
      editButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            editAnnotation();
         }
      });
      if (separatorLabel != null) {
         // The resizeListener sets the correct layout data to ensure that the separator has the same height as the buttons
         ControlListener resizeListener = new ControlListener() {
            @Override
            public void controlResized(ControlEvent e) {
               separatorLabel.setLayoutData(new RowData(separatorLabel.getSize().x, editButton.getSize().y));
               composite.layout();
               editButton.removeControlListener(this);
            }
            
            @Override
            public void controlMoved(ControlEvent e) {
            }
         };
         editButton.addControlListener(resizeListener);
      }
      linksButton = getWidgetFactory().createButton(actionComposite, "", SWT.PUSH);
      linksButton.setToolTipText("Show annotation links.");
      linksButton.setImage(SEDImages.getImage(SEDImages.ANNOTATION_LINKS));
      linksButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            showAnnotationLinks();
         }
      });
      upButton = getWidgetFactory().createButton(actionComposite, "", SWT.PUSH);
      upButton.setToolTipText("Move selected annotations up.");
      upButton.setImage(SEDImages.getImage(SEDImages.ANNOTATION_MOVE_UP));
      upButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            moveAnnotationsUp();
         }
      });
      downButton = getWidgetFactory().createButton(actionComposite, "", SWT.PUSH);
      downButton.setToolTipText("Move selected annotations down.");
      downButton.setImage(SEDImages.getImage(SEDImages.ANNOTATION_MOVE_DOWN));
      downButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            moveAnnotationsDown();
         }
      });
      deleteButton = getWidgetFactory().createButton(actionComposite, "", SWT.PUSH);
      deleteButton.setToolTipText("Delete selected annotations.");
      deleteButton.setImage(SEDImages.getImage(SEDImages.ANNOTATION_DELETE));
      deleteButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            deleteAnnotations();
         }
      });
      // Add annotation viewer
      annoationsViewer = CheckboxTableViewer.newCheckList(composite, SWT.BORDER | SWT.MULTI | SWT.CHECK | SWT.V_SCROLL);
      annoationsViewer.getControl().setLayoutData(new GridData(GridData.FILL_BOTH));
      annoationsContentProvider = new AnnotationContentProvider();
      annoationsViewer.setContentProvider(annoationsContentProvider);
      annoationsViewer.addSelectionChangedListener(new ISelectionChangedListener() {
         @Override
         public void selectionChanged(SelectionChangedEvent event) {
            updateEditButtonsEnablement();
         }
      });
      MenuManager annoationLinksViewerMenuManager = new MenuManager();
      editAction = new Action("&Edit", SEDImages.getImageDescriptor(SEDImages.ANNOTATION_EDIT)) {
         @Override
         public void run() {
            editAnnotation();
         }
      };
      annoationLinksViewerMenuManager.add(editAction);
      linksAction = new Action("&Show annotation links", SEDImages.getImageDescriptor(SEDImages.ANNOTATION_LINKS)) {
         @Override
         public void run() {
            showAnnotationLinks();
         }
      };
      annoationLinksViewerMenuManager.add(linksAction);
      upAction = new Action("Move &up", SEDImages.getImageDescriptor(SEDImages.ANNOTATION_MOVE_UP)) {
         @Override
         public void run() {
            moveAnnotationsUp();
         }
      };
      annoationLinksViewerMenuManager.add(upAction);
      downAction = new Action("&Move down", SEDImages.getImageDescriptor(SEDImages.ANNOTATION_MOVE_DOWN)) {
         @Override
         public void run() {
            moveAnnotationsDown();
         }
      };
      annoationLinksViewerMenuManager.add(downAction);
      deleteAction = new Action("&Delete", SEDImages.getImageDescriptor(SEDImages.ANNOTATION_DELETE)) {
         @Override
         public void run() {
            deleteAnnotations();
         }
      };
      annoationLinksViewerMenuManager.add(deleteAction);
      annoationsViewer.getControl().setMenu(annoationLinksViewerMenuManager.createContextMenu(annoationsViewer.getControl()));
      annoationsViewer.addDoubleClickListener(new IDoubleClickListener() {
         @Override
         public void doubleClick(DoubleClickEvent event) {
            handleDoubleClick(event);
         }
      });
      updateEditButtonsEnablement();
   }

   /**
    * A double click was performed on {@link #annoationsViewer}.
    * @param event The event.
    */
   protected void handleDoubleClick(DoubleClickEvent event) {
      showAnnotationLinks();
   }
   
   /**
    * Edits the currently selected {@link ISEDAnnotation}.
    */
   public void editAnnotation() {
      Object obj = SWTUtil.getFirstElement(annoationsViewer.getSelection());
      if (obj instanceof ISEDAnnotation) {
         EditWizard.openWizard(editButton.getShell(), target, (ISEDAnnotation)obj);
      }
   }

   /**
    * Shows the links of an {@link ISEDAnnotation}.
    */
   public void showAnnotationLinks() {
      Object obj = SWTUtil.getFirstElement(annoationsViewer.getSelection());
      if (obj instanceof ISEDAnnotation) {
         AnnotationLinksDialog dialog = new AnnotationLinksDialog(linksButton.getShell(), target, (ISEDAnnotation)obj);
         dialog.setBlockOnOpen(false);
         dialog.setHelpAvailable(false);
         dialog.open();
      }
   }

   /**
    * Moves selected {@link ISEDAnnotation}s one up.
    */
   public void moveAnnotationsUp() {
      Object[] selected = SWTUtil.toArray(annoationsViewer.getSelection());
      for (Object obj : selected) {
         if (obj instanceof ISEDAnnotation) {
            ISEDAnnotation annotation = (ISEDAnnotation)obj;
            int index = target.indexOfRegisteredAnnotation(annotation);
            if (index >= 1) {
               target.moveRegisteredAnnotation(annotation, index - 1);
            }
         }
      }
      updateEditButtonsEnablement();
   }

   /**
    * Moves selected {@link ISEDAnnotation}s one down.
    */
   public void moveAnnotationsDown() {
      Object[] selected = SWTUtil.toArray(annoationsViewer.getSelection());
      for (int i = selected.length - 1; i >= 0; i--) {
         if (selected[i] instanceof ISEDAnnotation) {
            ISEDAnnotation annotation = (ISEDAnnotation)selected[i];
            int index = target.indexOfRegisteredAnnotation(annotation);
            if (index < target.countRegisteredAnnotations() - 1) {
               target.moveRegisteredAnnotation(annotation, index + 1);
            }
         }
      }
      updateEditButtonsEnablement();
   }
   
   /**
    * Deletes selected {@link ISEDAnnotation}s.
    */
   public void deleteAnnotations() {
      Object[] selected = SWTUtil.toArray(annoationsViewer.getSelection());
      for (Object obj : selected) {
         if (obj instanceof ISEDAnnotation) {
            ISEDAnnotation annotation = (ISEDAnnotation)obj;
            annotation.delete(target);
         }
      }
   }

   /**
    * Updates the enabled state of the edit buttons.
    */
   protected void updateEditButtonsEnablement() {
      Object[] selected = SWTUtil.toArray(annoationsViewer.getSelection());
      // Compute enabled states
      boolean canMoveUp = false;
      boolean canMoveDown = false;
      boolean canDelete = false;
      int i = 0;
      while (i < selected.length && (!canMoveUp || !canMoveDown || !canDelete)) {
         if (selected[i] instanceof ISEDAnnotation) {
            ISEDAnnotation annotation = (ISEDAnnotation)selected[i];
            if (!canMoveUp || !canMoveDown) {
               int index = target.indexOfRegisteredAnnotation(annotation);
               if (!canMoveUp && index >= 1) {
                  canMoveUp = true;
               }
               if (!canMoveDown && index < target.countRegisteredAnnotations() - 1) {
                  canMoveDown = true;
               }
            }
            if (!canDelete && annotation.canDelete(target)) {
               canDelete = true;
            }
         }
         i++;
      }
      // Update enabled states
      editButton.setEnabled(selected.length == 1);
      linksButton.setEnabled(selected.length == 1);
      upButton.setEnabled(canMoveUp);
      downButton.setEnabled(canMoveDown);
      deleteButton.setEnabled(canDelete);
      editAction.setEnabled(selected.length == 1);
      linksAction.setEnabled(selected.length == 1);
      upAction.setEnabled(canMoveUp);
      downAction.setEnabled(canMoveDown);
      deleteAction.setEnabled(canDelete);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void refresh() {
      super.refresh();
      target = getDebugTarget();
      if (annotationsLabelProvider != null) {
         annotationsLabelProvider.dispose();
      }
      if (annotationsSelectionSynchronizer != null) {
         annotationsSelectionSynchronizer.dispose();
      }
      if (annotationsColorSynchronizer != null) {
         annotationsColorSynchronizer.dispose();
      }
      annoationsViewer.setInput(target);
      annotationsLabelProvider = new AnnotationLabelProvider(target);
      annoationsViewer.setLabelProvider(annotationsLabelProvider);
      annotationsSelectionSynchronizer = new AnnotationCheckedStateSynchronizer(target, annoationsViewer);
      annotationsColorSynchronizer = new AnnotationColorTableSynchronizer(target, annoationsViewer);
      for (Button button : actionButtons) {
         button.setEnabled(target != null);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      if (annoationsContentProvider != null) {
         annoationsContentProvider.dispose();
      }
      if (annotationsLabelProvider != null) {
         annotationsLabelProvider.dispose();
      }
      if (annotationsSelectionSynchronizer != null) {
         annotationsSelectionSynchronizer.dispose();
      }
      if (annotationsColorSynchronizer != null) {
         annotationsColorSynchronizer.dispose();
      }
      super.dispose();
   }
}
