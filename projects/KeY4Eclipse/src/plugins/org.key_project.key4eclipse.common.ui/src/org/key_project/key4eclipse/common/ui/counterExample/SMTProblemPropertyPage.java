package org.key_project.key4eclipse.common.ui.counterExample;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.TabFolder;
import org.eclipse.swt.widgets.TabItem;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.dialogs.PropertyPage;
import org.key_project.util.java.ArrayUtil;

import de.uka.ilkd.key.gui.smt.CETree;
import de.uka.ilkd.key.gui.smt.InformationWindow;
import de.uka.ilkd.key.gui.smt.InformationWindow.Information;
import de.uka.ilkd.key.gui.smt.SolverListener.InternSMTProblem;
import de.uka.ilkd.key.smt.SolverType;
import de.uka.ilkd.key.smt.model.Heap;
import de.uka.ilkd.key.smt.model.LocationSet;
import de.uka.ilkd.key.smt.model.Model;
import de.uka.ilkd.key.smt.model.ObjectVal;
import de.uka.ilkd.key.smt.model.Sequence;

/**
 * A {@link PropertyPage} which shows the result of an {@link InternSMTProblem}.
 * @author Martin Hentschel
 */
public class SMTProblemPropertyPage extends PropertyPage {
   /**
    * The solved {@link InternSMTProblem}.
    */
   private final InternSMTProblem problem;
   
   /**
    * Constructor.
    * @param problem The solved {@link InternSMTProblem}.
    */
   public SMTProblemPropertyPage(InternSMTProblem problem) {
      this.problem = problem;
      noDefaultAndApplyButton();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected Control createContents(Composite parent) {
      TabFolder tabFolder = new TabFolder(parent, SWT.NONE);
      if (problem.getSolver().getType() == SolverType.Z3_CE_SOLVER &&
          problem.getSolver().getSocket().getQuery() != null) {
         Model model = problem.getSolver().getSocket().getQuery().getModel();
         model.removeUnnecessaryObjects();
         model.addAliases();
         createTreeViewerTab(tabFolder, "Counterexample", new ModelContentProvider(), new ModelLabelProvider(), model);
         createTextTab(tabFolder, "Help", InformationWindow.CE_HELP);
      }
      for (Information information : problem.getInformation()) {
         createTextTab(tabFolder, information.getTitle(), information.getContent());
      }
      if (tabFolder.getItemCount() >= 1) {
         tabFolder.setSelection(tabFolder.getItem(0));
      }
      return tabFolder;
   }
   
   /**
    * Creates a {@link TabItem} which shows a text.
    * @param tabFolder The parent {@link TabFolder}.
    * @param title The tab title.
    * @param content The text to show.
    */
   protected void createTextTab(TabFolder tabFolder, 
                                String title, 
                                String content) {
      Text text = new Text(tabFolder, SWT.MULTI | SWT.READ_ONLY);
      text.setText(content);
      TabItem item = new TabItem(tabFolder, SWT.NONE);
      item.setText(title);
      item.setControl(text);
   }
   
   /**
    * Creates a {@link TabItem} which shows a {@link TreeViewer}.
    * @param tabFolder The parent {@link TabFolder}.
    * @param title The tab title.
    * @param contentProvider The {@link ITreeContentProvider} to use.
    * @param labelProvider The {@link ILabelProvider} to use.
    * @param input The input to show.
    */
   protected void createTreeViewerTab(TabFolder tabFolder, 
                                      String title, 
                                      ITreeContentProvider contentProvider, 
                                      ILabelProvider labelProvider,
                                      Object input) {
      TreeViewer viewer = new TreeViewer(tabFolder, SWT.MULTI);
      viewer.setContentProvider(contentProvider);
      viewer.setLabelProvider(labelProvider);
      viewer.setInput(input);
      TabItem item = new TabItem(tabFolder, SWT.NONE);
      item.setText(title);
      item.setControl(viewer.getControl());
      tabFolder.setSelection(item);
   }
   
   /**
    * An {@link ITreeContentProvider} which shows the structure of a {@link Model}.
    * @author Martin Hentschel
    */
   protected static class ModelContentProvider implements ITreeContentProvider {
      /**
       * {@inheritDoc}
       */
      @Override
      public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Object[] getChildren(Object parentElement) {
         if (parentElement instanceof Model) {
            List<Object> children = new LinkedList<Object>();
            Model model = (Model) parentElement;
            if (!model.getConstants().isEmpty()) {
               children.add(new CollectionFolder("Constants", CETree.computeConstantLabels(model)));
            }
            if (!model.getHeaps().isEmpty()) {
               children.add(new CollectionFolder("Heaps", model.getHeaps()));
            }
            if (!model.getLocsets().isEmpty()) {
               children.add(new CollectionFolder("Location Sets", model.getLocsets()));
            }
            if (!model.getSequences().isEmpty()) {
               children.add(new CollectionFolder("Sequences", model.getSequences()));
            }
            return children.toArray();
         }
         else if (parentElement instanceof CollectionFolder) {
            return ((CollectionFolder) parentElement).getChildren();
         }
         else if (parentElement instanceof Heap) {
            return ((Heap) parentElement).getObjects().toArray();
         }
         else if (parentElement instanceof ObjectVal) {
            ObjectVal ov = (ObjectVal) parentElement;
            List<Object> children = new LinkedList<Object>();
            String sortName = CETree.computeSortName(ov);
            // General properties
            children.addAll(CETree.computeObjectProperties(ov, sortName));
            //Fields
            children.add(new CollectionFolder("Fields", CETree.computeFields(ov)));
            //Array Fields
            if (CETree.hasArrayFields(sortName)) {
               children.add(new CollectionFolder("Array Fields", CETree.computeArrayFields(ov)));
            }
            //Fun Values
            children.add(new CollectionFolder("Functions", CETree.computeFunctions(ov)));
            return children.toArray();
         }
         else if (parentElement instanceof LocationSet) {
            return CETree.computeLocationSetProperties((LocationSet) parentElement).toArray();
         }
         else if (parentElement instanceof Sequence) {
            return CETree.computeSequenceProperties((Sequence) parentElement).toArray();
         }
         else {
            return new Object[0];
         }
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Object[] getElements(Object inputElement) {
         return getChildren(inputElement);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Object getParent(Object element) {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public boolean hasChildren(Object element) {
         return !ArrayUtil.isEmpty(getChildren(element));
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void dispose() {
      }
   }
   
   /**
    * An {@link ILabelProvider} which shows {@link Model} elements.
    * @author Martin Hentschel
    */
   protected static class ModelLabelProvider extends LabelProvider {
      /**
       * {@inheritDoc}
       */
      @Override
      public String getText(Object element) {
         if (element instanceof Sequence) {
            return CETree.computeSequenceName((Sequence) element);
         }
         else if (element instanceof LocationSet) {
            return CETree.computeLocationSetName((LocationSet) element);
         }
         else if (element instanceof Heap) {
            return ((Heap) element).getName();
         }
         else if (element instanceof ObjectVal) {
            return ((ObjectVal) element).getName();
         }
         else {
            return super.getText(element);
         }
      }
   }
   
   /**
    * Utility class used by {@link ModelContentProvider} and
    * {@link ModelLabelProvider} to show the structure of a {@link Model}.
    * @author Martin Hentschel
    */
   protected static class CollectionFolder {
      /**
       * The text.
       */
      private final String text;
      
      /**
       * The children.
       */
      private final Collection<?> children;

      /**
       * Constructor.
       * @param text The text.
       * @param children The children.
       */
      public CollectionFolder(String text, Collection<?> children) {
         this.text = text;
         this.children = children;
      }

      /**
       * Returns the children.
       * @return The children.
       */
      public Object[] getChildren() {
         return children.toArray();
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String toString() {
         return text;
      }
   }
}
