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

package org.key_project.sed.key.ui.property;

import java.util.Arrays;
import java.util.Comparator;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.DisposeEvent;
import org.eclipse.swt.events.DisposeListener;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.services.IDisposable;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetWidgetFactory;
import org.key_project.key4eclipse.common.ui.decorator.ProofSourceViewerDecorator;
import org.key_project.key4eclipse.common.ui.decorator.TruthValueTracingViewerDecorator;
import org.key_project.key4eclipse.common.ui.util.LogUtil;
import org.key_project.sed.key.core.model.IKeYSENode;
import org.key_project.sed.key.core.util.KeYSEDPreferences;
import org.key_project.sed.key.ui.preference.page.KeYColorsPreferencePage;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.eclipse.job.AbstractDependingOnObjectsJob;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.ObjectUtil;

import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.label.FormulaTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.AbstractOperationPO;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.TruthValueTracingUtil;
import de.uka.ilkd.key.symbolic_execution.TruthValueTracingUtil.BranchResult;
import de.uka.ilkd.key.symbolic_execution.TruthValueTracingUtil.MultiEvaluationResult;
import de.uka.ilkd.key.symbolic_execution.TruthValueTracingUtil.TruthValue;
import de.uka.ilkd.key.symbolic_execution.TruthValueTracingUtil.TruthValueTracingResult;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;

/**
 * This composite provides the content shown in {@link AbstractTruthValuePropertySection}
 * and {@link AbstractTruthValueGraphitiPropertySection}.
 * @author Martin Hentschel
 */
public abstract class AbstractTruthValueComposite implements IDisposable {
   /**
    * Indicates if updates are included or not.
    */
   public static final boolean INCLUDE_UPDATES = true;
   
   /**
    * The {@link TabbedPropertySheetWidgetFactory} to use.
    */
   private final TabbedPropertySheetWidgetFactory factory;
   
   /**
    * An optional {@link ILayoutListener} invoked when the shown content has changed.
    */
   private final ILayoutListener layoutListener;
   
   /**
    * The root {@link Composite}.
    */
   private final Composite root;
   
   /**
    * The children of {@link #root}.
    */
   private final List<Control> controls = new LinkedList<Control>();
   
   /**
    * The used {@link TruthValueTracingViewerDecorator}s.
    */
   private final List<TruthValueTracingViewerDecorator> decorators = new LinkedList<TruthValueTracingViewerDecorator>();

   /**
    * The {@link Color} to highlight {@link TruthValue#TRUE}.
    */
   private Color trueColor;

   /**
    * The {@link Color} to highlight {@link TruthValue#FALSE}.
    */
   private Color falseColor;

   /**
    * The {@link Color} to highlight {@link TruthValue#UNKNOWN} or {@code null}.
    */
   private Color unknownColor;
   
   /**
    * The currently shown {@link IKeYSENode}.
    */
   private IKeYSENode<?> currentNode;
   
   /**
    * Listens for color changes
    */
   private final IPropertyChangeListener colorPropertyListener = new IPropertyChangeListener() {
      @Override
      public void propertyChange(PropertyChangeEvent event) {
         handleColorPropertyChange(event);
      }
   };
   
   /**
    * Listens for editor changes.
    */
   private IPropertyChangeListener editorsListener = new IPropertyChangeListener() {
      @Override
      public void propertyChange(PropertyChangeEvent event) {
         handleEditorPropertyChange(event);
      }
   };
   
   /**
    * Constructor.
    * @param parent The parent {@link Composite}.
    * @param factory The {@link TabbedPropertySheetWidgetFactory} to use.
    * @param layoutListener An optional {@link ILayoutListener} invoked when the shown content has changed.
    */
   public AbstractTruthValueComposite(Composite parent, TabbedPropertySheetWidgetFactory factory, ILayoutListener layoutListener) {
      this.factory = factory;
      this.layoutListener = layoutListener;
      root = factory.createFlatFormComposite(parent);
      root.setLayout(new GridLayout(1, false));
      updateColors();
      KeYSEDPreferences.getStore().addPropertyChangeListener(colorPropertyListener);
      SWTUtil.getEditorsPreferenceStore().addPropertyChangeListener(editorsListener);
      JFaceResources.getFontRegistry().addListener(editorsListener);
   }

   protected void handleColorPropertyChange(PropertyChangeEvent event) {
      if (KeYSEDPreferences.TRUTH_VALUE_TRACING_TRUE.equals(event.getProperty())
          || KeYSEDPreferences.TRUTH_VALUE_TRACING_FALSE.equals(event.getProperty())
          || KeYSEDPreferences.TRUTH_VALUE_TRACING_UNKNOWN.equals(event.getProperty())) {
         updateColors();
         recreateContent();
      }
   }
   
   /**
    * Updates the used colors.
    */
   protected void updateColors() {
      if (trueColor != null) {
         trueColor.dispose();
      }
      trueColor = new Color(root.getDisplay(), KeYSEDPreferences.getTruthValueTracingTrue());
      if (falseColor != null) {
         falseColor.dispose();
      }
      falseColor = new Color(root.getDisplay(), KeYSEDPreferences.getTruthValueTracingFalse());
      if (unknownColor != null) {
         unknownColor.dispose();
      }
      unknownColor = new Color(root.getDisplay(), KeYSEDPreferences.getTruthValueTracingUnknown());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      KeYSEDPreferences.getStore().removePropertyChangeListener(colorPropertyListener);
      SWTUtil.getEditorsPreferenceStore().removePropertyChangeListener(editorsListener);
      JFaceResources.getFontRegistry().removeListener(editorsListener);
      if (trueColor != null) {
         trueColor.dispose();
      }
      if (falseColor != null) {
         falseColor.dispose();
      }
      if (unknownColor != null) {
         unknownColor.dispose();
      }
   }

   protected void handleEditorPropertyChange(PropertyChangeEvent event) {
      if (event.getProperty().equals(SWTUtil.getEditorsTextFontPropertiesKey())) {
         recreateContent();
      }
   }
   
   /**
    * Updates the shown content.
    * @param node The {@link IKeYSENode} which provides the new content.
    */
   public void updateContent(final IKeYSENode<?> node) {
      if (!ObjectUtil.equals(currentNode, node)) {
         currentNode = node;
         recreateContent();
      }
   }
   
   /**
    * Recreates the shown content.
    */
   protected void recreateContent() {
      showEvaluatingInformation();
      AbstractDependingOnObjectsJob.cancelJobs(this);
      Job job = new AbstractDependingOnObjectsJob("Evaluating postconditions", this, PlatformUI.getWorkbench()) {
         @Override
         protected IStatus run(IProgressMonitor monitor) {
            try {
               computeAndAddNewContent(currentNode);
               return Status.OK_STATUS;
            }
            catch (OperationCanceledException e) {
               return Status.CANCEL_STATUS;
            }
            catch (Exception e) {
               return LogUtil.getLogger().createErrorStatus(e);
            }
         }
      };
      job.setSystem(true);
      job.schedule();
   }

   /**
    * Shows an information message to the user.
    */
   protected void showEvaluatingInformation() {
      removeOldContent();
      Label label = factory.createLabel(root, "Please wait until postcondition is evaluated.");
      controls.add(label);
      updateLayout();
   }

   /**
    * Removes all old content and disposes it.
    */
   protected void removeOldContent() {
      for (ProofSourceViewerDecorator viewerDecorator : decorators) {
         viewerDecorator.dispose();
      }
      decorators.clear();
      for (Control control : controls) {
         control.setVisible(false);
         control.dispose();
      }
      controls.clear();
   }
   
   /**
    * Shows new content.
    * @param node The {@link IKeYSENode} which provides the new content.
    */
   protected void computeAndAddNewContent(final IKeYSENode<?> node) {
      try {
         if (node != null) {
            // Get required information
            final IExecutionNode<?> executionNode = node.getExecutionNode();
            final Node keyNode = computeNodeToShow(node, executionNode);
            final Triple<Term, PosInTerm, Term> triple = computeTermToShow(node, executionNode, keyNode);
            // Compute result
            ITreeSettings settings = node.getExecutionNode().getSettings();
            final TruthValueTracingResult result = TruthValueTracingUtil.evaluate(keyNode, 
                                                                                  FormulaTermLabel.NAME,
                                                                                  settings.isUseUnicode(),
                                                                                  settings.isUsePrettyPrinting());
            if (!root.isDisposed()) {
               root.getDisplay().syncExec(new Runnable() {
                  @Override
                  public void run() {
                     if (!root.isDisposed()) {
                        addNewContent(result, triple.first, triple.second, triple.third, executionNode);
                     }
                  }
               });
            }
         }
      }
      catch (final ProofInputException e) {
         if (!root.isDisposed()) {
            root.getDisplay().syncExec(new Runnable() {
               @Override
               public void run() {
                  if (!root.isDisposed()) {
                     Text text = factory.createText(root, e.getMessage());
                     text.setEditable(false);
                     controls.add(text);
                  }
               }
            });
         }
      }
   }
   
   /**
    * Computes the {@link Node} to show.
    * @param node The {@link IKeYSENode}.
    * @param executionNode The {@link IExecutionNode}.
    * @return The {@link Node} to show.
    */
   protected Node computeNodeToShow(IKeYSENode<?> node, IExecutionNode<?> executionNode) {
      return executionNode.getProofNode();
   }
   
   /**
    * Computes the {@link Sequent} to show.
    * @param antecedent The antecedent.
    * @param succedent The succedent.
    * @return The created {@link Sequent}.
    */
   protected Sequent createSequentToShow(Term antecedent,
                                         Term succedent) {
      Sequent sequent = Sequent.EMPTY_SEQUENT;
      sequent = sequent.addFormula(new SequentFormula(antecedent), true, false).sequent();
      sequent = sequent.addFormula(new SequentFormula(succedent), false, false).sequent();
      return sequent;
   }
   
   /**
    * Computes the {@link Term} to show.
    * @param node The {@link IKeYSENode}.
    * @param executionNode The {@link IExecutionNode}.
    * @param keyNode The {@link Node}.
    * @return The {@link Term} to show and optionally the {@link PosInTerm} of the uninterpreted predicate and the base of the {@link PosInTerm}.
    */
   protected abstract Triple<Term, PosInTerm, Term> computeTermToShow(IKeYSENode<?> node, 
                                                                      IExecutionNode<?> executionNode, 
                                                                      Node keyNode);

   /**
    * Shows the given content.
    * @param result The {@link TruthValueTracingResult} to consider.
    * @param succedent The {@link Term} to show as succedent.
    * @param uninterpretedPredicatePosition The optional {@link PosInTerm} with the uninterpreted predicate.
    * @param uninterpretedPredicateGroundTerm The {@link Term} in which the {@link PosInTerm} is evaluated in.
    * @param node The {@link IKeYSENode} which provides the new content.
    */
   protected void addNewContent(TruthValueTracingResult result,
                                Term succedent,
                                PosInTerm uninterpretedPredicatePosition,
                                Term uninterpretedPredicateGroundTerm,
                                IExecutionNode<?> executionNode) {
      removeOldContent();
      BranchResult[] branchResults = result.getBranchResults();
      Arrays.sort(branchResults, new Comparator<BranchResult>() { // Sort branch result to ensure that open nodes are shown first
         @Override
         public int compare(BranchResult o1, BranchResult o2) {
            boolean o1closed = o1.getLeafNode().isClosed();
            boolean o2closed = o2.getLeafNode().isClosed();
            if (o1closed && !o2closed) {
               return 1;
            }
            else if (!o1closed && o2closed) {
               return -1;
            }
            else {
               return 0;
            }
         }
      });
      Color notConsideredColor = null;
      for (BranchResult branchResult : branchResults) {
         if (shouldShowBranchResult(branchResult, uninterpretedPredicatePosition, uninterpretedPredicateGroundTerm)) {
            // Remove uninterpreted predicate from expressions. Currently, only the AND operator is supported and should be needed.
            if (uninterpretedPredicatePosition != null) {
               PosInTerm currentPosition = uninterpretedPredicatePosition;
               final Term uninterpretedPredicate = currentPosition.getSubTerm(uninterpretedPredicateGroundTerm);
               while (currentPosition != null) {
                  Term currentTerm = currentPosition.getSubTerm(uninterpretedPredicateGroundTerm);
                  FormulaTermLabel label = (FormulaTermLabel)currentTerm.getLabel(FormulaTermLabel.NAME);
                  MultiEvaluationResult labelResult = branchResult.getResult(label);
                  if (labelResult != null) {
                     Term instructionTerm = labelResult.getInstructionTerm();
                     if (instructionTerm != null && instructionTerm.op() == Junctor.AND) {
                        if (instructionTerm.sub(0).op() == uninterpretedPredicate.op()) {
                           instructionTerm = instructionTerm.sub(1);
                           labelResult = labelResult.newInstructionTerm(instructionTerm);
                           branchResult.updateResult(label, labelResult);
                        }
                        else if (instructionTerm.sub(1).op() == uninterpretedPredicate.op()) {
                           instructionTerm = instructionTerm.sub(0);
                           labelResult = labelResult.newInstructionTerm(instructionTerm);
                           branchResult.updateResult(label, labelResult);
                        }
                     }
                  }
                  currentPosition = currentPosition.up();
               }
            }
            // Create group
            Group viewerGroup = factory.createGroup(root, "Node " + branchResult.getLeafNode().serialNr());
            viewerGroup.setLayout(new FillLayout());
            viewerGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
            controls.add(viewerGroup);
            // Create viewer
            SourceViewer viewer = new SourceViewer(viewerGroup, null, SWT.MULTI | SWT.FULL_SELECTION);
            viewer.setEditable(false);
            final Font font = SWTUtil.initializeViewerFont(viewer);
            viewer.getTextWidget().addDisposeListener(new DisposeListener() {
               @Override
               public void widgetDisposed(DisposeEvent e) {
                  if (font != null) {
                     font.dispose();
                  }
               }
            });
            notConsideredColor = viewer.getTextWidget().getForeground();
            TruthValueTracingViewerDecorator viewerDecorator = new TruthValueTracingViewerDecorator(viewer, trueColor.getRGB(), falseColor.getRGB(), unknownColor.getRGB());
            decorators.add(viewerDecorator);
            // Show term and results
            Sequent sequent = createSequentToShow(branchResult.getCondition(), succedent);
            TruthValue value = viewerDecorator.showSequent(sequent, 
                                                           executionNode.getServices(), 
                                                           SymbolicExecutionUtil.createNotationInfo(executionNode), 
                                                           branchResult);
            viewerGroup.setBackground(viewerDecorator.getColor(value));
         }
      }
      // Add legend
      addLegend(notConsideredColor);
      // Layout root
      updateLayout();
   }

   /**
    * Check is the given {@link BranchResult} should be shown.
    * @param branchResult The {@link BranchResult} to check.
    * @param uninterpretedPredicatePosition The uninterpreted predicate which provides the {@link FormulaTermLabel}.
    * @param uninterpretedPredicateGroundTerm The {@link Term} in which the {@link PosInTerm} is evaluated in.
    * @return {@code true} show branch result, {@code false} do not show branch result.
    */
   protected boolean shouldShowBranchResult(BranchResult branchResult, PosInTerm uninterpretedPredicatePosition, Term uninterpretedPredicateGroundTerm) {
      if (branchResult != null) {
         if (uninterpretedPredicatePosition != null) {
            Term uninterpretedPredicate = uninterpretedPredicatePosition.getSubTerm(uninterpretedPredicateGroundTerm);
            TermLabel label = uninterpretedPredicate.getLabel(FormulaTermLabel.NAME);
            if (label instanceof FormulaTermLabel) {
               TruthValue result = branchResult.evaluate((FormulaTermLabel) label);
               return result == null || !TruthValue.FALSE.equals(result);
            }
            else {
               return true;
            }
         }
         else {
            return true;
         }
      }
      else {
         return false;
      }
   }
   
   /**
    * Searches the {@link Term} with the uninterpreted predicate.
    * @param term The {@link Term} to start search at.
    * @param uninterpretedPredicate The {@link Term} of the proof obligation which specifies the uninterpreted predicate.
    * @return The {@link PosInTerm} of the uninterpreted predicate.
    */
   protected PosInTerm findUninterpretedPredicateTerm(Term term, Term uninterpretedPredicate) {
      return findUninterpretedPredicateTerm(term, uninterpretedPredicate, PosInTerm.getTopLevel());
   }
      
   /**
    * Searches the {@link Term} with the uninterpreted predicate.
    * @param term The {@link Term} to start search at.
    * @param uninterpretedPredicate The {@link Term} of the proof obligation which specifies the uninterpreted predicate.
    * @return The {@link PosInTerm} of the uninterpreted predicate.
    */
   protected PosInTerm findUninterpretedPredicateTerm(Term term, Term uninterpretedPredicate, PosInTerm current) {
      if (uninterpretedPredicate != null) {
         if (term.op() == uninterpretedPredicate.op()) {
            return current;
         }
         else if (term.op() == Junctor.AND) {
            PosInTerm result = null;
            int i = 0;
            while (result == null && i < term.arity()) {
               result = findUninterpretedPredicateTerm(term.sub(i), uninterpretedPredicate, current.down(i));
               i++;
            }
            return result;
         }
         else {
            return null;
         }
      }
      else {
         return null;
      }
   }

   /**
    * Ensures that the right content is shown.
    */
   protected void updateLayout() {
      root.layout();
      root.getParent().pack();
      root.getParent().layout();
      if (layoutListener != null) {
         layoutListener.layoutUpdated();
      }
   }

   /**
    * Removes the uninterpreted predicate if required.
    * @param node The {@link Node}.
    * @param term The {@link Term}.
    * @return The {@link Term} without the uninterpreted predicate.
    */
   protected Term removeUninterpretedPredicate(Node node, Term term) {
      Proof proof = node.proof();
      Term predicate = AbstractOperationPO.getUninterpretedPredicate(proof);
      if (predicate != null) {
         term = removeUninterpretedPredicate(proof.getServices().getTermBuilder(), 
                                             term, 
                                             predicate);
      }
      return term;
   }

   /**
    * Removes the uninterpreted predicate recursively in the {@code and} structure.
    * @param tb The {@link TermBuilder} to use.
    * @param term The current {@link Term}.
    * @param uninterpretedPredicate The uninterpreted predicate to remove.
    * @return The {@link Term} without the uninterpreted predicate. 
    */
   protected Term removeUninterpretedPredicate(TermBuilder tb, 
                                               Term term, 
                                               Term uninterpretedPredicate) {
      if (uninterpretedPredicate.op() == term.op()) {
         return tb.tt();
      }
      else if (term.op() == Junctor.AND) { // Only and is supported to ensure correct results
         boolean subsChanged = false;
         Term[] newSubs = new Term[term.arity()];
         for (int i = 0; i < newSubs.length; i++) {
            Term sub = term.sub(i);
            newSubs[i] = removeUninterpretedPredicate(tb, sub, uninterpretedPredicate);
            if (sub != newSubs[i]) {
               subsChanged = true;
            }
         }
         if (subsChanged) {
            Term newTerm = tb.and(newSubs);
            if (term.hasLabels() && newSubs[0] != newTerm && newSubs[1] != newTerm) { // Label new Term only if all children are still important.
               newTerm = tb.label(newTerm, term.getLabels());
            }
            return newTerm;
         }
         else {
            return term;
         }
      }
      else if (term.op() == UpdateApplication.UPDATE_APPLICATION) {
         Pair<ImmutableList<Term>, Term> pair = TermBuilder.goBelowUpdates2(term);
         Term newTarget = removeUninterpretedPredicate(tb, pair.second, uninterpretedPredicate);
         if (pair.second != newTarget) {
            Term newTerm = tb.applyParallel(pair.first, newTarget);
            if (term.hasLabels()) {
               newTerm = tb.label(newTerm, term.getLabels());
            }
            return newTerm;
         }
         else {
            return term;
         }
      }
      else {
         return term;
      }
   }

   /**
    * Adds the legend.
    */
   protected void addLegend(Color notConsideredColor) {
      // Create context menu
      MenuManager manager = new MenuManager();
      manager.add(new Action("Change &Colors...") {
         @Override
         public void run() {
            openColorPreferencePage();
         }
      });
      // Create legend
      Composite legendComposite = factory.createFlatFormComposite(root);
      legendComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      GridLayout legendLayout = new GridLayout(5, false);
      legendLayout.marginBottom = 0;
      legendLayout.marginHeight = 0;
      legendLayout.marginLeft = 0;
      legendLayout.marginRight = 0;
      legendLayout.marginWidth = 0;
      legendLayout.verticalSpacing = 0;
      legendComposite.setLayout(legendLayout);
      controls.add(legendComposite);
      Label legendLabel = factory.createLabel(legendComposite, "Legend: ");
      legendLabel.setMenu(manager.createContextMenu(legendLabel));
      Label trueLabel = factory.createLabel(legendComposite, "true");
      trueLabel.setForeground(trueColor);
      trueLabel.setToolTipText("The term evaluates to true.");
      trueLabel.setMenu(manager.createContextMenu(trueLabel));
      Label falseLabel = factory.createLabel(legendComposite, "false");
      falseLabel.setForeground(falseColor);
      falseLabel.setToolTipText("The term evaluates to false.");
      falseLabel.setMenu(manager.createContextMenu(falseLabel));
      Label unknownLabel = factory.createLabel(legendComposite, "unknown");
      unknownLabel.setForeground(unknownColor);
      unknownLabel.setToolTipText("The term is not (yet) completely evaluated into true or false.");
      unknownLabel.setMenu(manager.createContextMenu(unknownLabel));
      Label notConsideredLabel = factory.createLabel(legendComposite, "not considered");
      notConsideredLabel.setForeground(notConsideredColor);
      notConsideredLabel.setToolTipText("The term is not part of the truth value tracing.");
      notConsideredLabel.setMenu(manager.createContextMenu(notConsideredLabel));
   }
   
   /**
    * Opens the preference page to change the colors.
    */
   protected void openColorPreferencePage() {
      KeYColorsPreferencePage.openPreferencePage(root.getShell());
   }

   public static interface ILayoutListener {
      public void layoutUpdated();
   }
}